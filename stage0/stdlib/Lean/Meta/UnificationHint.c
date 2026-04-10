// Lean compiler output
// Module: Lean.Meta.UnificationHint
// Imports: public import Lean.Meta.SynthInstance
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_getResetPostponed___redArg(lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_instToFormatName__lean___lam__0(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_format___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
static const lean_array_object l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry_default = (const lean_object*)&l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry = (const lean_object*)&l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedUnificationHints_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHints_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHints;
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instToFormatUnificationHints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToFormatName__lean___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instToFormatUnificationHints___closed__0 = (const lean_object*)&l_Lean_Meta_instToFormatUnificationHints___closed__0_value;
static const lean_closure_object l_Lean_Meta_instToFormatUnificationHints___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instToFormatUnificationHints___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_instToFormatUnificationHints___closed__0_value)} };
static const lean_object* l_Lean_Meta_instToFormatUnificationHints___closed__1 = (const lean_object*)&l_Lean_Meta_instToFormatUnificationHints___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instToFormatUnificationHints = (const lean_object*)&l_Lean_Meta_instToFormatUnificationHints___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 0, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unificationHintExtension"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 204, 145, 124, 244, 133, 63, 146)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_UnificationHints_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unificationHintExtension;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__0 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1_value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "invalid unification hint constraint, unexpected term"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object*);
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "invalid unification hint constraint, unexpected dependency"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "invalid unification hint, failed to unify constraint left-hand-side"};
static const lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0 = (const lean_object*)&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0_value;
static lean_once_cell_t l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1;
static const lean_string_object l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "\nwith right-hand-side"};
static const lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2 = (const lean_object*)&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2_value;
static lean_once_cell_t l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3;
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "invalid unification hint, failed to unify pattern left-hand-side"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_addUnificationHint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "invalid unification hint, it must be a definition"};
static const lean_object* l_Lean_Meta_addUnificationHint___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_addUnificationHint___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_addUnificationHint___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addUnificationHint___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "UnificationHint"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 112, 70, 159, 80, 199, 244, 3)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 201, 225, 55, 169, 192, 235, 23)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 76, 73, 18, 200, 34, 166, 102)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 195, 224, 136, 81, 175, 205, 78)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 1, 154, 40, 227, 230, 26, 25)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 208, 18, 32, 63, 140, 98, 77)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 91, 67, 57, 71, 246, 20, 20)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 2, 155, 161, 116, 126, 168, 23)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 237, 31, 132, 39, 246, 206, 71)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unification_hint"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 153, 150, 74, 163, 227, 238, 154)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unification hint"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0;
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1;
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isDefEq"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3_value;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hint"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4_value;
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 173, 228, 229, 125, 117, 225, 10)}};
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(115, 131, 150, 64, 79, 8, 33, 190)}};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6_value;
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_value;
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = " succeeded, applying constraints"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9_value;
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hint "};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at "};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints_default(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints___lam__0(lean_object* v___f_11_, lean_object* v_h_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Meta_DiscrTree_format___redArg(v___f_11_, v_h_12_);
return v___x_13_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0));
v___x_25_ = l_Lean_Meta_Config_toConfigWithKey(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config(void){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
lean_object* v_ks_31_; lean_object* v_vs_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_56_; 
v_ks_31_ = lean_ctor_get(v_x_27_, 0);
v_vs_32_ = lean_ctor_get(v_x_27_, 1);
v_isSharedCheck_56_ = !lean_is_exclusive(v_x_27_);
if (v_isSharedCheck_56_ == 0)
{
v___x_34_ = v_x_27_;
v_isShared_35_ = v_isSharedCheck_56_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_vs_32_);
lean_inc(v_ks_31_);
lean_dec(v_x_27_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_56_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = lean_array_get_size(v_ks_31_);
v___x_37_ = lean_nat_dec_lt(v_x_28_, v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
lean_dec(v_x_28_);
v___x_38_ = lean_array_push(v_ks_31_, v_x_29_);
v___x_39_ = lean_array_push(v_vs_32_, v_x_30_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v___x_39_);
lean_ctor_set(v___x_34_, 0, v___x_38_);
v___x_41_ = v___x_34_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
else
{
lean_object* v_k_x27_43_; uint8_t v___x_44_; 
v_k_x27_43_ = lean_array_fget_borrowed(v_ks_31_, v_x_28_);
v___x_44_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_29_, v_k_x27_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_46_; 
if (v_isShared_35_ == 0)
{
v___x_46_ = v___x_34_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_ks_31_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_vs_32_);
v___x_46_ = v_reuseFailAlloc_50_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_x_28_, v___x_47_);
lean_dec(v_x_28_);
v_x_27_ = v___x_46_;
v_x_28_ = v___x_48_;
goto _start;
}
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_51_ = lean_array_fset(v_ks_31_, v_x_28_, v_x_29_);
v___x_52_ = lean_array_fset(v_vs_32_, v_x_28_, v_x_30_);
lean_dec(v_x_28_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v___x_52_);
lean_ctor_set(v___x_34_, 0, v___x_51_);
v___x_54_ = v___x_34_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_51_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_n_57_, lean_object* v_k_58_, lean_object* v_v_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_57_, v___x_60_, v_k_58_, v_v_59_);
return v___x_61_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_62_; size_t v___x_63_; size_t v___x_64_; 
v___x_62_ = ((size_t)5ULL);
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_shift_left(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_65_; size_t v___x_66_; size_t v___x_67_; 
v___x_65_ = ((size_t)1ULL);
v___x_66_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_67_ = lean_usize_sub(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(lean_object* v_x_69_, size_t v_x_70_, size_t v_x_71_, lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v_es_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v_j_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_es_74_ = lean_ctor_get(v_x_69_, 0);
v___x_75_ = ((size_t)5ULL);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_78_ = lean_usize_land(v_x_70_, v___x_77_);
v_j_79_ = lean_usize_to_nat(v___x_78_);
v___x_80_ = lean_array_get_size(v_es_74_);
v___x_81_ = lean_nat_dec_lt(v_j_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_dec(v_j_79_);
lean_dec(v_x_73_);
lean_dec(v_x_72_);
return v_x_69_;
}
else
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_118_; 
lean_inc_ref(v_es_74_);
v_isSharedCheck_118_ = !lean_is_exclusive(v_x_69_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v_x_69_, 0);
lean_dec(v_unused_119_);
v___x_83_ = v_x_69_;
v_isShared_84_ = v_isSharedCheck_118_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_x_69_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_118_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_v_85_; lean_object* v___x_86_; lean_object* v_xs_x27_87_; lean_object* v___y_89_; 
v_v_85_ = lean_array_fget(v_es_74_, v_j_79_);
v___x_86_ = lean_box(0);
v_xs_x27_87_ = lean_array_fset(v_es_74_, v_j_79_, v___x_86_);
switch(lean_obj_tag(v_v_85_))
{
case 0:
{
lean_object* v_key_94_; lean_object* v_val_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_105_; 
v_key_94_ = lean_ctor_get(v_v_85_, 0);
v_val_95_ = lean_ctor_get(v_v_85_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_v_85_);
if (v_isSharedCheck_105_ == 0)
{
v___x_97_ = v_v_85_;
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_val_95_);
lean_inc(v_key_94_);
lean_dec(v_v_85_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
uint8_t v___x_99_; 
v___x_99_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_72_, v_key_94_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_del_object(v___x_97_);
v___x_100_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_94_, v_val_95_, v_x_72_, v_x_73_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___y_89_ = v___x_101_;
goto v___jp_88_;
}
else
{
lean_object* v___x_103_; 
lean_dec(v_val_95_);
lean_dec(v_key_94_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v_x_73_);
lean_ctor_set(v___x_97_, 0, v_x_72_);
v___x_103_ = v___x_97_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_x_72_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_x_73_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
v___y_89_ = v___x_103_;
goto v___jp_88_;
}
}
}
}
case 1:
{
lean_object* v_node_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_116_; 
v_node_106_ = lean_ctor_get(v_v_85_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v_v_85_);
if (v_isSharedCheck_116_ == 0)
{
v___x_108_ = v_v_85_;
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_node_106_);
lean_dec(v_v_85_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
size_t v___x_110_; size_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_110_ = lean_usize_shift_right(v_x_70_, v___x_75_);
v___x_111_ = lean_usize_add(v_x_71_, v___x_76_);
v___x_112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_node_106_, v___x_110_, v___x_111_, v_x_72_, v_x_73_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_112_);
v___x_114_ = v___x_108_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
v___y_89_ = v___x_114_;
goto v___jp_88_;
}
}
}
default: 
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v_x_72_);
lean_ctor_set(v___x_117_, 1, v_x_73_);
v___y_89_ = v___x_117_;
goto v___jp_88_;
}
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = lean_array_fset(v_xs_x27_87_, v_j_79_, v___y_89_);
lean_dec(v_j_79_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_90_);
v___x_92_ = v___x_83_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
else
{
lean_object* v_ks_120_; lean_object* v_vs_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_141_; 
v_ks_120_ = lean_ctor_get(v_x_69_, 0);
v_vs_121_ = lean_ctor_get(v_x_69_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_x_69_);
if (v_isSharedCheck_141_ == 0)
{
v___x_123_ = v_x_69_;
v_isShared_124_ = v_isSharedCheck_141_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_vs_121_);
lean_inc(v_ks_120_);
lean_dec(v_x_69_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_141_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_ks_120_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_vs_121_);
v___x_126_ = v_reuseFailAlloc_140_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v_newNode_127_; uint8_t v___y_129_; size_t v___x_135_; uint8_t v___x_136_; 
v_newNode_127_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(v___x_126_, v_x_72_, v_x_73_);
v___x_135_ = ((size_t)7ULL);
v___x_136_ = lean_usize_dec_le(v___x_135_, v_x_71_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_127_);
v___x_138_ = lean_unsigned_to_nat(4u);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
lean_dec(v___x_137_);
v___y_129_ = v___x_139_;
goto v___jp_128_;
}
else
{
v___y_129_ = v___x_136_;
goto v___jp_128_;
}
v___jp_128_:
{
if (v___y_129_ == 0)
{
lean_object* v_ks_130_; lean_object* v_vs_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_ks_130_ = lean_ctor_get(v_newNode_127_, 0);
lean_inc_ref(v_ks_130_);
v_vs_131_ = lean_ctor_get(v_newNode_127_, 1);
lean_inc_ref(v_vs_131_);
lean_dec_ref(v_newNode_127_);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2);
v___x_134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_x_71_, v_ks_130_, v_vs_131_, v___x_132_, v___x_133_);
lean_dec_ref(v_vs_131_);
lean_dec_ref(v_ks_130_);
return v___x_134_;
}
else
{
return v_newNode_127_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(size_t v_depth_142_, lean_object* v_keys_143_, lean_object* v_vals_144_, lean_object* v_i_145_, lean_object* v_entries_146_){
_start:
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_array_get_size(v_keys_143_);
v___x_148_ = lean_nat_dec_lt(v_i_145_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec(v_i_145_);
return v_entries_146_;
}
else
{
lean_object* v_k_149_; lean_object* v_v_150_; uint64_t v___x_151_; size_t v_h_152_; size_t v___x_153_; lean_object* v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; size_t v_h_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_k_149_ = lean_array_fget_borrowed(v_keys_143_, v_i_145_);
v_v_150_ = lean_array_fget_borrowed(v_vals_144_, v_i_145_);
v___x_151_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_149_);
v_h_152_ = lean_uint64_to_usize(v___x_151_);
v___x_153_ = ((size_t)5ULL);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_sub(v_depth_142_, v___x_155_);
v___x_157_ = lean_usize_mul(v___x_153_, v___x_156_);
v_h_158_ = lean_usize_shift_right(v_h_152_, v___x_157_);
v___x_159_ = lean_nat_add(v_i_145_, v___x_154_);
lean_dec(v_i_145_);
lean_inc(v_v_150_);
lean_inc(v_k_149_);
v___x_160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_entries_146_, v_h_158_, v_depth_142_, v_k_149_, v_v_150_);
v_i_145_ = v___x_159_;
v_entries_146_ = v___x_160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_162_, lean_object* v_keys_163_, lean_object* v_vals_164_, lean_object* v_i_165_, lean_object* v_entries_166_){
_start:
{
size_t v_depth_boxed_167_; lean_object* v_res_168_; 
v_depth_boxed_167_ = lean_unbox_usize(v_depth_162_);
lean_dec(v_depth_162_);
v_res_168_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_167_, v_keys_163_, v_vals_164_, v_i_165_, v_entries_166_);
lean_dec_ref(v_vals_164_);
lean_dec_ref(v_keys_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_x_173_){
_start:
{
size_t v_x_1605__boxed_174_; size_t v_x_1606__boxed_175_; lean_object* v_res_176_; 
v_x_1605__boxed_174_ = lean_unbox_usize(v_x_170_);
lean_dec(v_x_170_);
v_x_1606__boxed_175_ = lean_unbox_usize(v_x_171_);
lean_dec(v_x_171_);
v_res_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_169_, v_x_1605__boxed_174_, v_x_1606__boxed_175_, v_x_172_, v_x_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
uint64_t v___x_180_; size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; 
v___x_180_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_178_);
v___x_181_ = lean_uint64_to_usize(v___x_180_);
v___x_182_ = ((size_t)1ULL);
v___x_183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_177_, v___x_181_, v___x_182_, v_x_178_, v_x_179_);
return v___x_183_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
lean_object* v_fst_186_; lean_object* v_fst_187_; uint8_t v___x_188_; 
v_fst_186_ = lean_ctor_get(v_a_184_, 0);
v_fst_187_ = lean_ctor_get(v_b_185_, 0);
v___x_188_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_186_, v_fst_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_189_, lean_object* v_b_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_a_189_, v_b_190_);
lean_dec_ref(v_b_190_);
lean_dec_ref(v_a_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(lean_object* v_x_193_, lean_object* v_keys_194_, lean_object* v_v_195_, lean_object* v_k_196_, lean_object* v_x_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v_c_200_; lean_object* v___x_201_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_add(v_x_193_, v___x_198_);
v_c_200_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_194_, v_v_195_, v___x_199_);
lean_dec(v___x_199_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v_k_196_);
lean_ctor_set(v___x_201_, 1, v_c_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_202_, lean_object* v_keys_203_, lean_object* v_v_204_, lean_object* v_k_205_, lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_202_, v_keys_203_, v_v_204_, v_k_205_, v_x_206_);
lean_dec_ref(v_keys_203_);
lean_dec(v_x_202_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5_spec__10(lean_object* v_vs_208_, lean_object* v_v_209_, lean_object* v_i_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_array_get_size(v_vs_208_);
v___x_212_ = lean_nat_dec_lt(v_i_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_dec(v_i_210_);
v___x_213_ = lean_array_push(v_vs_208_, v_v_209_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_array_fget_borrowed(v_vs_208_, v_i_210_);
v___x_215_ = lean_name_eq(v_v_209_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v_i_210_, v___x_216_);
lean_dec(v_i_210_);
v_i_210_ = v___x_217_;
goto _start;
}
else
{
lean_object* v___x_219_; 
v___x_219_ = lean_array_fset(v_vs_208_, v_i_210_, v_v_209_);
lean_dec(v_i_210_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5(lean_object* v_vs_220_, lean_object* v_v_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5_spec__10(v_vs_220_, v_v_221_, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(lean_object* v_x_228_, lean_object* v_keys_229_, lean_object* v_v_230_, lean_object* v_k_231_, lean_object* v_as_232_, lean_object* v_k_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v_mid_238_; lean_object* v_midVal_239_; uint8_t v___x_240_; 
v___x_236_ = lean_nat_add(v_x_234_, v_x_235_);
v___x_237_ = lean_unsigned_to_nat(1u);
v_mid_238_ = lean_nat_shiftr(v___x_236_, v___x_237_);
lean_dec(v___x_236_);
v_midVal_239_ = lean_array_fget(v_as_232_, v_mid_238_);
v___x_240_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_midVal_239_, v_k_233_);
if (v___x_240_ == 0)
{
uint8_t v___x_241_; 
lean_dec(v_x_235_);
v___x_241_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_k_233_, v_midVal_239_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; uint8_t v___x_243_; 
lean_dec(v_x_234_);
v___x_242_ = lean_array_get_size(v_as_232_);
v___x_243_ = lean_nat_dec_lt(v_mid_238_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v_midVal_239_);
lean_dec(v_mid_238_);
lean_dec(v_k_231_);
lean_dec(v_v_230_);
return v_as_232_;
}
else
{
lean_object* v_snd_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_256_; 
v_snd_244_ = lean_ctor_get(v_midVal_239_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_midVal_239_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v_midVal_239_, 0);
lean_dec(v_unused_257_);
v___x_246_ = v_midVal_239_;
v_isShared_247_ = v_isSharedCheck_256_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_snd_244_);
lean_dec(v_midVal_239_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_256_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v_xs_x27_249_; lean_object* v___x_250_; lean_object* v_c_251_; lean_object* v___x_253_; 
v___x_248_ = lean_box(0);
v_xs_x27_249_ = lean_array_fset(v_as_232_, v_mid_238_, v___x_248_);
v___x_250_ = lean_nat_add(v_x_228_, v___x_237_);
v_c_251_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_229_, v_v_230_, v___x_250_, v_snd_244_);
lean_dec(v___x_250_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v_c_251_);
lean_ctor_set(v___x_246_, 0, v_k_231_);
v___x_253_ = v___x_246_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_k_231_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_c_251_);
v___x_253_ = v_reuseFailAlloc_255_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; 
v___x_254_ = lean_array_fset(v_xs_x27_249_, v_mid_238_, v___x_253_);
lean_dec(v_mid_238_);
return v___x_254_;
}
}
}
}
else
{
lean_dec(v_midVal_239_);
v_x_235_ = v_mid_238_;
goto _start;
}
}
else
{
uint8_t v___x_259_; 
lean_dec(v_midVal_239_);
v___x_259_ = lean_nat_dec_eq(v_mid_238_, v_x_234_);
if (v___x_259_ == 0)
{
lean_dec(v_x_234_);
v_x_234_ = v_mid_238_;
goto _start;
}
else
{
lean_object* v___x_261_; lean_object* v_c_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_j_265_; lean_object* v_as_266_; lean_object* v___x_267_; 
lean_dec(v_mid_238_);
lean_dec(v_x_235_);
v___x_261_ = lean_nat_add(v_x_228_, v___x_237_);
v_c_262_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_229_, v_v_230_, v___x_261_);
lean_dec(v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v_k_231_);
lean_ctor_set(v___x_263_, 1, v_c_262_);
v___x_264_ = lean_nat_add(v_x_234_, v___x_237_);
lean_dec(v_x_234_);
v_j_265_ = lean_array_get_size(v_as_232_);
v_as_266_ = lean_array_push(v_as_232_, v___x_263_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_264_, v_as_266_, v_j_265_);
lean_dec(v___x_264_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(lean_object* v_x_268_, lean_object* v_keys_269_, lean_object* v_v_270_, lean_object* v_k_271_, lean_object* v_as_272_, lean_object* v_k_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = lean_array_get_size(v_as_272_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_nat_dec_eq(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_array_fget_borrowed(v_as_272_, v___x_275_);
v___x_278_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_k_273_, v___x_277_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; 
v___x_279_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v___x_277_, v_k_273_);
if (v___x_279_ == 0)
{
uint8_t v___x_280_; 
v___x_280_ = lean_nat_dec_lt(v___x_275_, v___x_274_);
if (v___x_280_ == 0)
{
lean_dec(v_k_271_);
lean_dec(v_v_270_);
return v_as_272_;
}
else
{
lean_object* v___x_281_; lean_object* v_xs_x27_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_inc(v___x_277_);
v___x_281_ = lean_box(0);
v_xs_x27_282_ = lean_array_fset(v_as_272_, v___x_275_, v___x_281_);
v___x_283_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(v_x_268_, v_keys_269_, v_v_270_, v_k_271_, v___x_277_);
v___x_284_ = lean_array_fset(v_xs_x27_282_, v___x_275_, v___x_283_);
return v___x_284_;
}
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_sub(v___x_274_, v___x_285_);
v___x_287_ = lean_array_fget_borrowed(v_as_272_, v___x_286_);
v___x_288_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v___x_287_, v_k_273_);
if (v___x_288_ == 0)
{
uint8_t v___x_289_; 
v___x_289_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_k_273_, v___x_287_);
if (v___x_289_ == 0)
{
uint8_t v___x_290_; 
v___x_290_ = lean_nat_dec_lt(v___x_286_, v___x_274_);
if (v___x_290_ == 0)
{
lean_dec(v___x_286_);
lean_dec(v_k_271_);
lean_dec(v_v_270_);
return v_as_272_;
}
else
{
lean_object* v___x_291_; lean_object* v_xs_x27_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_inc(v___x_287_);
v___x_291_ = lean_box(0);
v_xs_x27_292_ = lean_array_fset(v_as_272_, v___x_286_, v___x_291_);
v___x_293_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(v_x_268_, v_keys_269_, v_v_270_, v_k_271_, v___x_287_);
v___x_294_ = lean_array_fset(v_xs_x27_292_, v___x_286_, v___x_293_);
lean_dec(v___x_286_);
return v___x_294_;
}
}
else
{
lean_object* v___x_295_; 
v___x_295_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_268_, v_keys_269_, v_v_270_, v_k_271_, v_as_272_, v_k_273_, v___x_275_, v___x_286_);
return v___x_295_;
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v___x_286_);
v___x_296_ = lean_box(0);
v___x_297_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_268_, v_keys_269_, v_v_270_, v_k_271_, v___x_296_);
v___x_298_ = lean_array_push(v_as_272_, v___x_297_);
return v___x_298_;
}
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_as_301_; lean_object* v___x_302_; 
v___x_299_ = lean_box(0);
v___x_300_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_268_, v_keys_269_, v_v_270_, v_k_271_, v___x_299_);
v_as_301_ = lean_array_push(v_as_272_, v___x_300_);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_275_, v_as_301_, v___x_274_);
return v___x_302_;
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_box(0);
v___x_304_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_268_, v_keys_269_, v_v_270_, v_k_271_, v___x_303_);
v___x_305_ = lean_array_push(v_as_272_, v___x_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(lean_object* v_keys_306_, lean_object* v_v_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_vs_310_; lean_object* v_children_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_328_; 
v_vs_310_ = lean_ctor_get(v_x_309_, 0);
v_children_311_ = lean_ctor_get(v_x_309_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_328_ == 0)
{
v___x_313_ = v_x_309_;
v_isShared_314_ = v_isSharedCheck_328_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_children_311_);
lean_inc(v_vs_310_);
lean_dec(v_x_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_328_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_array_get_size(v_keys_306_);
v___x_316_ = lean_nat_dec_lt(v_x_308_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5(v_vs_310_, v_v_307_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_317_);
v___x_319_ = v___x_313_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_children_311_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
else
{
lean_object* v_k_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_c_324_; lean_object* v___x_326_; 
v_k_321_ = lean_array_fget_borrowed(v_keys_306_, v_x_308_);
v___x_322_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__1));
lean_inc_n(v_k_321_, 2);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v_k_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v_c_324_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(v_x_308_, v_keys_306_, v_v_307_, v_k_321_, v_children_311_, v___x_323_);
lean_dec_ref(v___x_323_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v_c_324_);
v___x_326_ = v___x_313_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_vs_310_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_c_324_);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(lean_object* v_x_329_, lean_object* v_keys_330_, lean_object* v_v_331_, lean_object* v_k_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_snd_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_344_; 
v_snd_334_ = lean_ctor_get(v_x_333_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v_x_333_, 0);
lean_dec(v_unused_345_);
v___x_336_ = v_x_333_;
v_isShared_337_ = v_isSharedCheck_344_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snd_334_);
lean_dec(v_x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_344_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_c_340_; lean_object* v___x_342_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_add(v_x_329_, v___x_338_);
v_c_340_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_330_, v_v_331_, v___x_339_, v_snd_334_);
lean_dec(v___x_339_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_c_340_);
lean_ctor_set(v___x_336_, 0, v_k_332_);
v___x_342_ = v___x_336_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_k_332_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_c_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_346_, lean_object* v_keys_347_, lean_object* v_v_348_, lean_object* v_k_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(v_x_346_, v_keys_347_, v_v_348_, v_k_349_, v_x_350_);
lean_dec_ref(v_keys_347_);
lean_dec(v_x_346_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___boxed(lean_object* v_keys_352_, lean_object* v_v_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_352_, v_v_353_, v_x_354_, v_x_355_);
lean_dec(v_x_354_);
lean_dec_ref(v_keys_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_x_357_, lean_object* v_keys_358_, lean_object* v_v_359_, lean_object* v_k_360_, lean_object* v_as_361_, lean_object* v_k_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_357_, v_keys_358_, v_v_359_, v_k_360_, v_as_361_, v_k_362_, v_x_363_, v_x_364_);
lean_dec_ref(v_k_362_);
lean_dec_ref(v_keys_358_);
lean_dec(v_x_357_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___boxed(lean_object* v_x_366_, lean_object* v_keys_367_, lean_object* v_v_368_, lean_object* v_k_369_, lean_object* v_as_370_, lean_object* v_k_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(v_x_366_, v_keys_367_, v_v_368_, v_k_369_, v_as_370_, v_k_371_);
lean_dec_ref(v_k_371_);
lean_dec_ref(v_keys_367_);
lean_dec(v_x_366_);
return v_res_372_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3(lean_object* v_msg_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0);
v___x_376_ = lean_panic_fn_borrowed(v___x_375_, v_msg_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_377_, lean_object* v_vals_378_, lean_object* v_i_379_, lean_object* v_k_380_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_get_size(v_keys_377_);
v___x_382_ = lean_nat_dec_lt(v_i_379_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_i_379_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v_k_x27_384_; uint8_t v___x_385_; 
v_k_x27_384_ = lean_array_fget_borrowed(v_keys_377_, v_i_379_);
v___x_385_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_380_, v_k_x27_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_i_379_, v___x_386_);
lean_dec(v_i_379_);
v_i_379_ = v___x_387_;
goto _start;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_array_fget_borrowed(v_vals_378_, v_i_379_);
lean_dec(v_i_379_);
lean_inc(v___x_389_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_391_, lean_object* v_vals_392_, lean_object* v_i_393_, lean_object* v_k_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_391_, v_vals_392_, v_i_393_, v_k_394_);
lean_dec(v_k_394_);
lean_dec_ref(v_vals_392_);
lean_dec_ref(v_keys_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(lean_object* v_x_396_, size_t v_x_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_object* v_es_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_420_; 
v_es_399_ = lean_ctor_get(v_x_396_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_x_396_);
if (v_isSharedCheck_420_ == 0)
{
v___x_401_ = v_x_396_;
v_isShared_402_ = v_isSharedCheck_420_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_es_399_);
lean_dec(v_x_396_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_420_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; lean_object* v_j_407_; lean_object* v___x_408_; 
v___x_403_ = lean_box(2);
v___x_404_ = ((size_t)5ULL);
v___x_405_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_406_ = lean_usize_land(v_x_397_, v___x_405_);
v_j_407_ = lean_usize_to_nat(v___x_406_);
v___x_408_ = lean_array_get(v___x_403_, v_es_399_, v_j_407_);
lean_dec(v_j_407_);
lean_dec_ref(v_es_399_);
switch(lean_obj_tag(v___x_408_))
{
case 0:
{
lean_object* v_key_409_; lean_object* v_val_410_; uint8_t v___x_411_; 
v_key_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_key_409_);
v_val_410_ = lean_ctor_get(v___x_408_, 1);
lean_inc(v_val_410_);
lean_dec_ref(v___x_408_);
v___x_411_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_398_, v_key_409_);
lean_dec(v_key_409_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_dec(v_val_410_);
lean_del_object(v___x_401_);
v___x_412_ = lean_box(0);
return v___x_412_;
}
else
{
lean_object* v___x_414_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 1);
lean_ctor_set(v___x_401_, 0, v_val_410_);
v___x_414_ = v___x_401_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_val_410_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
case 1:
{
lean_object* v_node_416_; size_t v___x_417_; 
lean_del_object(v___x_401_);
v_node_416_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_node_416_);
lean_dec_ref(v___x_408_);
v___x_417_ = lean_usize_shift_right(v_x_397_, v___x_404_);
v_x_396_ = v_node_416_;
v_x_397_ = v___x_417_;
goto _start;
}
default: 
{
lean_object* v___x_419_; 
lean_del_object(v___x_401_);
v___x_419_ = lean_box(0);
return v___x_419_;
}
}
}
}
else
{
lean_object* v_ks_421_; lean_object* v_vs_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_ks_421_ = lean_ctor_get(v_x_396_, 0);
lean_inc_ref(v_ks_421_);
v_vs_422_ = lean_ctor_get(v_x_396_, 1);
lean_inc_ref(v_vs_422_);
lean_dec_ref(v_x_396_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_421_, v_vs_422_, v___x_423_, v_x_398_);
lean_dec_ref(v_vs_422_);
lean_dec_ref(v_ks_421_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
size_t v_x_2052__boxed_428_; lean_object* v_res_429_; 
v_x_2052__boxed_428_ = lean_unbox_usize(v_x_426_);
lean_dec(v_x_426_);
v_res_429_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_425_, v_x_2052__boxed_428_, v_x_427_);
lean_dec(v_x_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint64_t v___x_432_; size_t v___x_433_; lean_object* v___x_434_; 
v___x_432_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_431_);
v___x_433_ = lean_uint64_to_usize(v___x_432_);
v___x_434_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_430_, v___x_433_, v_x_431_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg___boxed(lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_x_435_, v_x_436_);
lean_dec(v_x_436_);
return v_res_437_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_441_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2));
v___x_442_ = lean_unsigned_to_nat(23u);
v___x_443_ = lean_unsigned_to_nat(166u);
v___x_444_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1));
v___x_445_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0));
v___x_446_ = l_mkPanicMessageWithDecl(v___x_445_, v___x_444_, v___x_443_, v___x_442_, v___x_441_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(lean_object* v_d_447_, lean_object* v_keys_448_, lean_object* v_v_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_array_get_size(v_keys_448_);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_nat_dec_eq(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v_k_454_; lean_object* v___x_455_; 
v___x_453_ = lean_box(0);
v_k_454_ = lean_array_get_borrowed(v___x_453_, v_keys_448_, v___x_451_);
lean_inc_ref(v_d_447_);
v___x_455_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_d_447_, v_k_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; lean_object* v_c_457_; lean_object* v___x_458_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v_c_457_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_448_, v_v_449_, v___x_456_);
lean_inc(v_k_454_);
v___x_458_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_d_447_, v_k_454_, v_c_457_);
return v___x_458_;
}
else
{
lean_object* v_val_459_; lean_object* v___x_460_; lean_object* v_c_461_; lean_object* v___x_462_; 
v_val_459_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_459_);
lean_dec_ref(v___x_455_);
v___x_460_ = lean_unsigned_to_nat(1u);
v_c_461_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_448_, v_v_449_, v___x_460_, v_val_459_);
lean_inc(v_k_454_);
v___x_462_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_d_447_, v_k_454_, v_c_461_);
return v___x_462_;
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_v_449_);
lean_dec_ref(v_d_447_);
v___x_463_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3);
v___x_464_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3(v___x_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___boxed(lean_object* v_d_465_, lean_object* v_keys_466_, lean_object* v_v_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_d_465_, v_keys_466_, v_v_467_);
lean_dec_ref(v_keys_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* v_hints_469_, lean_object* v_e_470_){
_start:
{
lean_object* v_keys_471_; lean_object* v_val_472_; lean_object* v___x_473_; 
v_keys_471_ = lean_ctor_get(v_e_470_, 0);
lean_inc_ref(v_keys_471_);
v_val_472_ = lean_ctor_get(v_e_470_, 1);
lean_inc(v_val_472_);
lean_dec_ref(v_e_470_);
v___x_473_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_hints_469_, v_keys_471_, v_val_472_);
lean_dec_ref(v_keys_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object* v_00_u03b2_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_x_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_00_u03b2_478_, v_x_479_, v_x_480_);
lean_dec(v_x_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(lean_object* v_00_u03b2_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_x_483_, v_x_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_487_, lean_object* v_x_488_, size_t v_x_489_, lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_488_, v_x_489_, v_x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_492_, lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
size_t v_x_2194__boxed_496_; lean_object* v_res_497_; 
v_x_2194__boxed_496_ = lean_unbox_usize(v_x_494_);
lean_dec(v_x_494_);
v_res_497_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(v_00_u03b2_492_, v_x_493_, v_x_2194__boxed_496_, v_x_495_);
lean_dec(v_x_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_498_, lean_object* v_x_499_, size_t v_x_500_, size_t v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_499_, v_x_500_, v_x_501_, v_x_502_, v_x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
size_t v_x_2205__boxed_511_; size_t v_x_2206__boxed_512_; lean_object* v_res_513_; 
v_x_2205__boxed_511_ = lean_unbox_usize(v_x_507_);
lean_dec(v_x_507_);
v_x_2206__boxed_512_ = lean_unbox_usize(v_x_508_);
lean_dec(v_x_508_);
v_res_513_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3(v_00_u03b2_505_, v_x_506_, v_x_2205__boxed_511_, v_x_2206__boxed_512_, v_x_509_, v_x_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_514_, lean_object* v_keys_515_, lean_object* v_vals_516_, lean_object* v_heq_517_, lean_object* v_i_518_, lean_object* v_k_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_515_, v_vals_516_, v_i_518_, v_k_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_521_, lean_object* v_keys_522_, lean_object* v_vals_523_, lean_object* v_heq_524_, lean_object* v_i_525_, lean_object* v_k_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_521_, v_keys_522_, v_vals_523_, v_heq_524_, v_i_525_, v_k_526_);
lean_dec(v_k_526_);
lean_dec_ref(v_vals_523_);
lean_dec_ref(v_keys_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_528_, lean_object* v_n_529_, lean_object* v_k_530_, lean_object* v_v_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(v_n_529_, v_k_530_, v_v_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_533_, size_t v_depth_534_, lean_object* v_keys_535_, lean_object* v_vals_536_, lean_object* v_heq_537_, lean_object* v_i_538_, lean_object* v_entries_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_534_, v_keys_535_, v_vals_536_, v_i_538_, v_entries_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_541_, lean_object* v_depth_542_, lean_object* v_keys_543_, lean_object* v_vals_544_, lean_object* v_heq_545_, lean_object* v_i_546_, lean_object* v_entries_547_){
_start:
{
size_t v_depth_boxed_548_; lean_object* v_res_549_; 
v_depth_boxed_548_ = lean_unbox_usize(v_depth_542_);
lean_dec(v_depth_542_);
v_res_549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_541_, v_depth_boxed_548_, v_keys_543_, v_vals_544_, v_heq_545_, v_i_546_, v_entries_547_);
lean_dec_ref(v_vals_544_);
lean_dec_ref(v_keys_543_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12(lean_object* v_x_550_, lean_object* v_keys_551_, lean_object* v_v_552_, lean_object* v_k_553_, lean_object* v_as_554_, lean_object* v_k_555_, lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_550_, v_keys_551_, v_v_552_, v_k_553_, v_as_554_, v_k_555_, v_x_556_, v_x_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_x_561_, lean_object* v_keys_562_, lean_object* v_v_563_, lean_object* v_k_564_, lean_object* v_as_565_, lean_object* v_k_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12(v_x_561_, v_keys_562_, v_v_563_, v_k_564_, v_as_565_, v_k_566_, v_x_567_, v_x_568_, v_x_569_, v_x_570_);
lean_dec_ref(v_k_566_);
lean_dec_ref(v_keys_562_);
lean_dec(v_x_561_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_572_, lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_573_, v_x_574_, v_x_575_, v_x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(uint8_t v_x_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v___y_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_x_581_, lean_object* v___y_582_){
_start:
{
uint8_t v_x_26__boxed_583_; lean_object* v_res_584_; 
v_x_26__boxed_583_ = lean_unbox(v_x_581_);
v_res_584_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v_x_26__boxed_583_, v___y_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object* v___y_585_){
_start:
{
lean_inc_ref(v___y_585_);
return v___y_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v___y_586_);
lean_dec_ref(v___y_586_);
return v_res_587_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___f_598_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___f_599_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_600_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___x_601_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_602_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___x_601_);
lean_ctor_set(v___x_603_, 2, v___x_600_);
lean_ctor_set(v___x_603_, 3, v___f_599_);
lean_ctor_set(v___x_603_, 4, v___f_598_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_);
v___x_606_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
return v_res_608_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2));
v___x_614_ = l_Lean_stringToMessageData(v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object* v_e_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1));
v___x_617_ = lean_unsigned_to_nat(3u);
v___x_618_ = l_Lean_Expr_isAppOfArity(v_e_615_, v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_619_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3);
v___x_620_ = l_Lean_indentExpr(v_e_615_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_623_ = l_Lean_Expr_appFn_x21(v_e_615_);
v___x_624_ = l_Lean_Expr_appArg_x21(v___x_623_);
lean_dec_ref(v___x_623_);
v___x_625_ = l_Lean_Expr_appArg_x21(v_e_615_);
lean_dec_ref(v_e_615_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object* v_e_631_, lean_object* v_cs_632_){
_start:
{
if (lean_obj_tag(v_e_631_) == 7)
{
lean_object* v_binderType_633_; lean_object* v_body_634_; lean_object* v___x_635_; 
v_binderType_633_ = lean_ctor_get(v_e_631_, 1);
v_body_634_ = lean_ctor_get(v_e_631_, 2);
lean_inc_ref(v_binderType_633_);
v___x_635_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_binderType_633_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v_e_631_);
lean_dec_ref(v_cs_632_);
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_657_; 
v_a_644_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_657_ == 0)
{
v___x_646_ = v___x_635_;
v_isShared_647_ = v_isSharedCheck_657_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_635_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_657_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; 
v___x_648_ = l_Lean_Expr_hasLooseBVars(v_body_634_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_inc_ref(v_body_634_);
lean_del_object(v___x_646_);
lean_dec_ref(v_e_631_);
v___x_649_ = lean_array_push(v_cs_632_, v_a_644_);
v_e_631_ = v_body_634_;
v_cs_632_ = v___x_649_;
goto _start;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
lean_dec(v_a_644_);
lean_dec_ref(v_cs_632_);
v___x_651_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1);
v___x_652_ = l_Lean_indentExpr(v_e_631_);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 0);
lean_ctor_set(v___x_646_, 0, v___x_653_);
v___x_655_ = v___x_646_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
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
else
{
lean_object* v___x_658_; 
v___x_658_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_e_631_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec_ref(v_cs_632_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_676_; 
v_a_667_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_676_ == 0)
{
v___x_669_ = v___x_658_;
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_658_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_671_ = lean_array_to_list(v_cs_632_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_a_667_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_672_);
v___x_674_ = v___x_669_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object* v_e_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0));
v___x_681_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(v_e_679_, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(lean_object* v_msgData_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_env_689_; lean_object* v___x_690_; lean_object* v_mctx_691_; lean_object* v_lctx_692_; lean_object* v_options_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_688_ = lean_st_ref_get(v___y_686_);
v_env_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref(v_env_689_);
lean_dec(v___x_688_);
v___x_690_ = lean_st_ref_get(v___y_684_);
v_mctx_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_mctx_691_);
lean_dec(v___x_690_);
v_lctx_692_ = lean_ctor_get(v___y_683_, 2);
v_options_693_ = lean_ctor_get(v___y_685_, 2);
lean_inc_ref(v_options_693_);
lean_inc_ref(v_lctx_692_);
v___x_694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_694_, 0, v_env_689_);
lean_ctor_set(v___x_694_, 1, v_mctx_691_);
lean_ctor_set(v___x_694_, 2, v_lctx_692_);
lean_ctor_set(v___x_694_, 3, v_options_693_);
v___x_695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_msgData_682_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object* v_msgData_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msgData_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(lean_object* v_msg_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_ref_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
v_ref_710_ = lean_ctor_get(v___y_707_, 5);
v___x_711_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_720_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
lean_inc(v_ref_710_);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v_ref_710_);
lean_ctor_set(v___x_716_, 1, v_a_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 1);
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg___boxed(lean_object* v_msg_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_727_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0));
v___x_730_ = l_Lean_stringToMessageData(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2));
v___x_733_ = l_Lean_stringToMessageData(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(lean_object* v_as_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
if (lean_obj_tag(v_as_734_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_box(0);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
else
{
lean_object* v_head_742_; lean_object* v_tail_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_777_; 
v_head_742_ = lean_ctor_get(v_as_734_, 0);
v_tail_743_ = lean_ctor_get(v_as_734_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_as_734_);
if (v_isSharedCheck_777_ == 0)
{
v___x_745_ = v_as_734_;
v_isShared_746_ = v_isSharedCheck_777_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_tail_743_);
lean_inc(v_head_742_);
lean_dec(v_as_734_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_777_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_lhs_747_; lean_object* v_rhs_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_776_; 
v_lhs_747_ = lean_ctor_get(v_head_742_, 0);
v_rhs_748_ = lean_ctor_get(v_head_742_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_head_742_);
if (v_isSharedCheck_776_ == 0)
{
v___x_750_ = v_head_742_;
v_isShared_751_ = v_isSharedCheck_776_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_rhs_748_);
lean_inc(v_lhs_747_);
lean_dec(v_head_742_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_776_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; 
lean_inc_ref(v_rhs_748_);
lean_inc_ref(v_lhs_747_);
v___x_752_ = l_Lean_Meta_isExprDefEq(v_lhs_747_, v_rhs_748_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; uint8_t v___x_754_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref(v___x_752_);
v___x_754_ = lean_unbox(v_a_753_);
lean_dec(v_a_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
lean_dec(v_tail_743_);
v___x_755_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1);
v___x_756_ = l_Lean_indentExpr(v_lhs_747_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 7);
lean_ctor_set(v___x_750_, 1, v___x_756_);
lean_ctor_set(v___x_750_, 0, v___x_755_);
v___x_758_ = v___x_750_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v___x_756_);
v___x_758_ = v_reuseFailAlloc_766_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 7);
lean_ctor_set(v___x_745_, 1, v___x_759_);
lean_ctor_set(v___x_745_, 0, v___x_758_);
v___x_761_ = v___x_745_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = l_Lean_indentExpr(v_rhs_748_);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_763_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_764_;
}
}
}
else
{
lean_del_object(v___x_750_);
lean_dec_ref(v_rhs_748_);
lean_dec_ref(v_lhs_747_);
lean_del_object(v___x_745_);
v_as_734_ = v_tail_743_;
goto _start;
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_del_object(v___x_750_);
lean_dec_ref(v_rhs_748_);
lean_dec_ref(v_lhs_747_);
lean_del_object(v___x_745_);
lean_dec(v_tail_743_);
v_a_768_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_752_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_752_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___boxed(lean_object* v_as_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_as_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_784_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object* v_hint_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_pattern_794_; lean_object* v_constraints_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_837_; 
v_pattern_794_ = lean_ctor_get(v_hint_788_, 0);
v_constraints_795_ = lean_ctor_get(v_hint_788_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_hint_788_);
if (v_isSharedCheck_837_ == 0)
{
v___x_797_ = v_hint_788_;
v_isShared_798_ = v_isSharedCheck_837_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_constraints_795_);
lean_inc(v_pattern_794_);
lean_dec(v_hint_788_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_837_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; 
v___x_799_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_constraints_795_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_lhs_800_; lean_object* v_rhs_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v___x_799_);
v_lhs_800_ = lean_ctor_get(v_pattern_794_, 0);
v_rhs_801_ = lean_ctor_get(v_pattern_794_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_pattern_794_);
if (v_isSharedCheck_836_ == 0)
{
v___x_803_ = v_pattern_794_;
v_isShared_804_ = v_isSharedCheck_836_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_rhs_801_);
lean_inc(v_lhs_800_);
lean_dec(v_pattern_794_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_836_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; 
lean_inc_ref(v_rhs_801_);
lean_inc_ref(v_lhs_800_);
v___x_805_ = l_Lean_Meta_isExprDefEq(v_lhs_800_, v_rhs_801_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_827_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_827_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_827_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_827_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
uint8_t v___x_810_; 
v___x_810_ = lean_unbox(v_a_806_);
lean_dec(v_a_806_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
lean_del_object(v___x_808_);
v___x_811_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1);
v___x_812_ = l_Lean_indentExpr(v_lhs_800_);
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 7);
lean_ctor_set(v___x_803_, 1, v___x_812_);
lean_ctor_set(v___x_803_, 0, v___x_811_);
v___x_814_ = v___x_803_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_822_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 7);
lean_ctor_set(v___x_797_, 1, v___x_815_);
lean_ctor_set(v___x_797_, 0, v___x_814_);
v___x_817_ = v___x_797_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = l_Lean_indentExpr(v_rhs_801_);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_819_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
return v___x_820_;
}
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_825_; 
lean_del_object(v___x_803_);
lean_dec_ref(v_rhs_801_);
lean_dec_ref(v_lhs_800_);
lean_del_object(v___x_797_);
v___x_823_ = lean_box(0);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_823_);
v___x_825_ = v___x_808_;
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
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_del_object(v___x_803_);
lean_dec_ref(v_rhs_801_);
lean_dec_ref(v_lhs_800_);
lean_del_object(v___x_797_);
v_a_828_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_805_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_805_);
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
}
else
{
lean_del_object(v___x_797_);
lean_dec_ref(v_pattern_794_);
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object* v_hint_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_hint_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object* v_00_u03b1_845_, lean_object* v_msg_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object* v_00_u03b1_853_, lean_object* v_msg_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(v_00_u03b1_853_, v_msg_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_860_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_861_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_867_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
lean_ctor_set(v___x_867_, 3, v___x_866_);
lean_ctor_set(v___x_867_, 4, v___x_866_);
lean_ctor_set(v___x_867_, 5, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(lean_object* v_ext_868_, lean_object* v_b_869_, uint8_t v_kind_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_currNamespace_875_; lean_object* v___x_876_; lean_object* v_env_877_; lean_object* v_nextMacroScope_878_; lean_object* v_ngen_879_; lean_object* v_auxDeclNGen_880_; lean_object* v_traceState_881_; lean_object* v_messages_882_; lean_object* v_infoState_883_; lean_object* v_snapshotTasks_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_911_; 
v_currNamespace_875_ = lean_ctor_get(v___y_872_, 6);
v___x_876_ = lean_st_ref_take(v___y_873_);
v_env_877_ = lean_ctor_get(v___x_876_, 0);
v_nextMacroScope_878_ = lean_ctor_get(v___x_876_, 1);
v_ngen_879_ = lean_ctor_get(v___x_876_, 2);
v_auxDeclNGen_880_ = lean_ctor_get(v___x_876_, 3);
v_traceState_881_ = lean_ctor_get(v___x_876_, 4);
v_messages_882_ = lean_ctor_get(v___x_876_, 6);
v_infoState_883_ = lean_ctor_get(v___x_876_, 7);
v_snapshotTasks_884_ = lean_ctor_get(v___x_876_, 8);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_876_, 5);
lean_dec(v_unused_912_);
v___x_886_ = v___x_876_;
v_isShared_887_ = v_isSharedCheck_911_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_snapshotTasks_884_);
lean_inc(v_infoState_883_);
lean_inc(v_messages_882_);
lean_inc(v_traceState_881_);
lean_inc(v_auxDeclNGen_880_);
lean_inc(v_ngen_879_);
lean_inc(v_nextMacroScope_878_);
lean_inc(v_env_877_);
lean_dec(v___x_876_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_911_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
lean_inc(v_currNamespace_875_);
v___x_888_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_877_, v_ext_868_, v_b_869_, v_kind_870_, v_currNamespace_875_);
v___x_889_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 5, v___x_889_);
lean_ctor_set(v___x_886_, 0, v___x_888_);
v___x_891_ = v___x_886_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_nextMacroScope_878_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_ngen_879_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_auxDeclNGen_880_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_traceState_881_);
lean_ctor_set(v_reuseFailAlloc_910_, 5, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_910_, 6, v_messages_882_);
lean_ctor_set(v_reuseFailAlloc_910_, 7, v_infoState_883_);
lean_ctor_set(v_reuseFailAlloc_910_, 8, v_snapshotTasks_884_);
v___x_891_ = v_reuseFailAlloc_910_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_mctx_894_; lean_object* v_zetaDeltaFVarIds_895_; lean_object* v_postponed_896_; lean_object* v_diag_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_908_; 
v___x_892_ = lean_st_ref_set(v___y_873_, v___x_891_);
v___x_893_ = lean_st_ref_take(v___y_871_);
v_mctx_894_ = lean_ctor_get(v___x_893_, 0);
v_zetaDeltaFVarIds_895_ = lean_ctor_get(v___x_893_, 2);
v_postponed_896_ = lean_ctor_get(v___x_893_, 3);
v_diag_897_ = lean_ctor_get(v___x_893_, 4);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v___x_893_, 1);
lean_dec(v_unused_909_);
v___x_899_ = v___x_893_;
v_isShared_900_ = v_isSharedCheck_908_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_diag_897_);
lean_inc(v_postponed_896_);
lean_inc(v_zetaDeltaFVarIds_895_);
lean_inc(v_mctx_894_);
lean_dec(v___x_893_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_908_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_mctx_894_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_zetaDeltaFVarIds_895_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_postponed_896_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_diag_897_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_st_ref_set(v___y_871_, v___x_903_);
v___x_905_ = lean_box(0);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(lean_object* v_ext_913_, lean_object* v_b_914_, lean_object* v_kind_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v_kind_boxed_920_; lean_object* v_res_921_; 
v_kind_boxed_920_ = lean_unbox(v_kind_915_);
v_res_921_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_913_, v_b_914_, v_kind_boxed_920_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object* v_00_u03b1_922_, lean_object* v_00_u03b2_923_, lean_object* v_00_u03c3_924_, lean_object* v_ext_925_, lean_object* v_b_926_, uint8_t v_kind_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_925_, v_b_926_, v_kind_927_, v___y_929_, v___y_930_, v___y_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object* v_00_u03b1_934_, lean_object* v_00_u03b2_935_, lean_object* v_00_u03c3_936_, lean_object* v_ext_937_, lean_object* v_b_938_, lean_object* v_kind_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
uint8_t v_kind_boxed_945_; lean_object* v_res_946_; 
v_kind_boxed_945_ = lean_unbox(v_kind_939_);
v_res_946_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(v_00_u03b1_934_, v_00_u03b2_935_, v_00_u03c3_936_, v_ext_937_, v_b_938_, v_kind_boxed_945_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(lean_object* v_k_947_, uint8_t v_allowLevelAssignments_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_948_, v_k_947_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
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
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_954_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_954_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(lean_object* v_k_971_, lean_object* v_allowLevelAssignments_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_978_; lean_object* v_res_979_; 
v_allowLevelAssignments_boxed_978_ = lean_unbox(v_allowLevelAssignments_972_);
v_res_979_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_971_, v_allowLevelAssignments_boxed_978_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(lean_object* v_00_u03b1_980_, lean_object* v_k_981_, uint8_t v_allowLevelAssignments_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_981_, v_allowLevelAssignments_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(lean_object* v_00_u03b1_989_, lean_object* v_k_990_, lean_object* v_allowLevelAssignments_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_997_; lean_object* v_res_998_; 
v_allowLevelAssignments_boxed_997_ = lean_unbox(v_allowLevelAssignments_991_);
v_res_998_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(v_00_u03b1_989_, v_k_990_, v_allowLevelAssignments_boxed_997_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
lean_ctor_set(v___x_1004_, 3, v___x_1003_);
lean_ctor_set(v___x_1004_, 4, v___x_1002_);
lean_ctor_set(v___x_1004_, 5, v___x_1002_);
lean_ctor_set(v___x_1004_, 6, v___x_1002_);
lean_ctor_set(v___x_1004_, 7, v___x_1002_);
lean_ctor_set(v___x_1004_, 8, v___x_1002_);
lean_ctor_set(v___x_1004_, 9, v___x_1002_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_unsigned_to_nat(32u);
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1008_ = ((size_t)5ULL);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = lean_unsigned_to_nat(32u);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_1010_);
v___x_1012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1013_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v___x_1011_);
lean_ctor_set(v___x_1013_, 2, v___x_1009_);
lean_ctor_set(v___x_1013_, 3, v___x_1009_);
lean_ctor_set_usize(v___x_1013_, 4, v___x_1008_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1014_ = lean_box(1);
v___x_1015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1016_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1015_);
lean_ctor_set(v___x_1017_, 2, v___x_1014_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1039_, lean_object* v_declHint_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_env_1044_; uint8_t v___x_1045_; 
v___x_1043_ = lean_st_ref_get(v___y_1041_);
v_env_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc_ref(v_env_1044_);
lean_dec(v___x_1043_);
v___x_1045_ = l_Lean_Name_isAnonymous(v_declHint_1040_);
if (v___x_1045_ == 0)
{
uint8_t v_isExporting_1046_; 
v_isExporting_1046_ = lean_ctor_get_uint8(v_env_1044_, sizeof(void*)*8);
if (v_isExporting_1046_ == 0)
{
lean_object* v___x_1047_; 
lean_dec_ref(v_env_1044_);
lean_dec(v_declHint_1040_);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_msg_1039_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
lean_inc_ref(v_env_1044_);
v___x_1048_ = l_Lean_Environment_setExporting(v_env_1044_, v___x_1045_);
lean_inc(v_declHint_1040_);
lean_inc_ref(v___x_1048_);
v___x_1049_ = l_Lean_Environment_contains(v___x_1048_, v_declHint_1040_, v_isExporting_1046_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_env_1044_);
lean_dec(v_declHint_1040_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_msg_1039_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_c_1056_; lean_object* v___x_1057_; 
v___x_1051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1053_ = l_Lean_Options_empty;
v___x_1054_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1048_);
lean_ctor_set(v___x_1054_, 1, v___x_1051_);
lean_ctor_set(v___x_1054_, 2, v___x_1052_);
lean_ctor_set(v___x_1054_, 3, v___x_1053_);
lean_inc(v_declHint_1040_);
v___x_1055_ = l_Lean_MessageData_ofConstName(v_declHint_1040_, v___x_1045_);
v_c_1056_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1056_, 0, v___x_1054_);
lean_ctor_set(v_c_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1044_, v_declHint_1040_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec_ref(v_env_1044_);
lean_dec(v_declHint_1040_);
v___x_1058_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v_c_1056_);
v___x_1060_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_MessageData_note(v___x_1061_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v_msg_1039_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1100_; 
v_val_1065_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1067_ = v___x_1057_;
v_isShared_1068_ = v_isSharedCheck_1100_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_val_1065_);
lean_dec(v___x_1057_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1100_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_mod_1072_; uint8_t v___x_1073_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = l_Lean_Environment_header(v_env_1044_);
lean_dec_ref(v_env_1044_);
v___x_1071_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1070_);
v_mod_1072_ = lean_array_get(v___x_1069_, v___x_1071_, v_val_1065_);
lean_dec(v_val_1065_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = l_Lean_isPrivateName(v_declHint_1040_);
lean_dec(v_declHint_1040_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1074_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v_c_1056_);
v___x_1076_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_MessageData_ofName(v_mod_1072_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_MessageData_note(v___x_1081_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v_msg_1039_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1083_);
v___x_1085_ = v___x_1067_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1087_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_c_1056_);
v___x_1089_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_MessageData_ofName(v_mod_1072_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_MessageData_note(v___x_1094_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v_msg_1039_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1096_);
v___x_1098_ = v___x_1067_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1101_; 
lean_dec_ref(v_env_1044_);
lean_dec(v_declHint_1040_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_msg_1039_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1102_, lean_object* v_declHint_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1102_, v_declHint_1103_, v___y_1104_);
lean_dec(v___y_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object* v_msg_1107_, lean_object* v_declHint_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1124_; 
v___x_1114_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1107_, v_declHint_1108_, v___y_1112_);
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1119_ = l_Lean_unknownIdentifierMessageTag;
v___x_1120_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_a_1115_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1125_, lean_object* v_declHint_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1125_, v_declHint_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1133_, lean_object* v_msg_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_fileName_1140_; lean_object* v_fileMap_1141_; lean_object* v_options_1142_; lean_object* v_currRecDepth_1143_; lean_object* v_maxRecDepth_1144_; lean_object* v_ref_1145_; lean_object* v_currNamespace_1146_; lean_object* v_openDecls_1147_; lean_object* v_initHeartbeats_1148_; lean_object* v_maxHeartbeats_1149_; lean_object* v_quotContext_1150_; lean_object* v_currMacroScope_1151_; uint8_t v_diag_1152_; lean_object* v_cancelTk_x3f_1153_; uint8_t v_suppressElabErrors_1154_; lean_object* v_inheritedTraceOptions_1155_; lean_object* v_ref_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_fileName_1140_ = lean_ctor_get(v___y_1137_, 0);
v_fileMap_1141_ = lean_ctor_get(v___y_1137_, 1);
v_options_1142_ = lean_ctor_get(v___y_1137_, 2);
v_currRecDepth_1143_ = lean_ctor_get(v___y_1137_, 3);
v_maxRecDepth_1144_ = lean_ctor_get(v___y_1137_, 4);
v_ref_1145_ = lean_ctor_get(v___y_1137_, 5);
v_currNamespace_1146_ = lean_ctor_get(v___y_1137_, 6);
v_openDecls_1147_ = lean_ctor_get(v___y_1137_, 7);
v_initHeartbeats_1148_ = lean_ctor_get(v___y_1137_, 8);
v_maxHeartbeats_1149_ = lean_ctor_get(v___y_1137_, 9);
v_quotContext_1150_ = lean_ctor_get(v___y_1137_, 10);
v_currMacroScope_1151_ = lean_ctor_get(v___y_1137_, 11);
v_diag_1152_ = lean_ctor_get_uint8(v___y_1137_, sizeof(void*)*14);
v_cancelTk_x3f_1153_ = lean_ctor_get(v___y_1137_, 12);
v_suppressElabErrors_1154_ = lean_ctor_get_uint8(v___y_1137_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1155_ = lean_ctor_get(v___y_1137_, 13);
v_ref_1156_ = l_Lean_replaceRef(v_ref_1133_, v_ref_1145_);
lean_inc_ref(v_inheritedTraceOptions_1155_);
lean_inc(v_cancelTk_x3f_1153_);
lean_inc(v_currMacroScope_1151_);
lean_inc(v_quotContext_1150_);
lean_inc(v_maxHeartbeats_1149_);
lean_inc(v_initHeartbeats_1148_);
lean_inc(v_openDecls_1147_);
lean_inc(v_currNamespace_1146_);
lean_inc(v_maxRecDepth_1144_);
lean_inc(v_currRecDepth_1143_);
lean_inc_ref(v_options_1142_);
lean_inc_ref(v_fileMap_1141_);
lean_inc_ref(v_fileName_1140_);
v___x_1157_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1157_, 0, v_fileName_1140_);
lean_ctor_set(v___x_1157_, 1, v_fileMap_1141_);
lean_ctor_set(v___x_1157_, 2, v_options_1142_);
lean_ctor_set(v___x_1157_, 3, v_currRecDepth_1143_);
lean_ctor_set(v___x_1157_, 4, v_maxRecDepth_1144_);
lean_ctor_set(v___x_1157_, 5, v_ref_1156_);
lean_ctor_set(v___x_1157_, 6, v_currNamespace_1146_);
lean_ctor_set(v___x_1157_, 7, v_openDecls_1147_);
lean_ctor_set(v___x_1157_, 8, v_initHeartbeats_1148_);
lean_ctor_set(v___x_1157_, 9, v_maxHeartbeats_1149_);
lean_ctor_set(v___x_1157_, 10, v_quotContext_1150_);
lean_ctor_set(v___x_1157_, 11, v_currMacroScope_1151_);
lean_ctor_set(v___x_1157_, 12, v_cancelTk_x3f_1153_);
lean_ctor_set(v___x_1157_, 13, v_inheritedTraceOptions_1155_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*14, v_diag_1152_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*14 + 1, v_suppressElabErrors_1154_);
v___x_1158_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_1134_, v___y_1135_, v___y_1136_, v___x_1157_, v___y_1138_);
lean_dec_ref(v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1159_, lean_object* v_msg_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1159_, v_msg_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v_ref_1159_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_ref_1167_, lean_object* v_msg_1168_, lean_object* v_declHint_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v_a_1176_; lean_object* v___x_1177_; 
v___x_1175_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1168_, v_declHint_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1167_, v_a_1176_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1178_, lean_object* v_msg_1179_, lean_object* v_declHint_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1178_, v_msg_1179_, v_declHint_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v_ref_1178_);
return v_res_1186_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1189_ = l_Lean_stringToMessageData(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1192_ = l_Lean_stringToMessageData(v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1193_, lean_object* v_constName_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1200_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1201_ = 0;
lean_inc(v_constName_1194_);
v___x_1202_ = l_Lean_MessageData_ofConstName(v_constName_1194_, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1200_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1193_, v___x_1205_, v_constName_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1207_, lean_object* v_constName_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1207_, v_constName_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v_ref_1207_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(lean_object* v_constName_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_ref_1221_; lean_object* v___x_1222_; 
v_ref_1221_ = lean_ctor_get(v___y_1218_, 5);
v___x_1222_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1221_, v_constName_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(lean_object* v_constName_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; lean_object* v_env_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = lean_st_ref_get(v___y_1234_);
v_env_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc_ref(v_env_1237_);
lean_dec(v___x_1236_);
v___x_1238_ = 0;
lean_inc(v_constName_1230_);
v___x_1239_ = l_Lean_Environment_find_x3f(v_env_1237_, v_constName_1230_, v___x_1238_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
return v___x_1240_;
}
else
{
lean_object* v_val_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_constName_1230_);
v_val_1241_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1239_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_val_1241_);
lean_dec(v___x_1239_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 0);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_val_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(lean_object* v_constName_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_constName_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1255_;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l_Lean_Meta_addUnificationHint___lam__0___closed__0));
v___x_1258_ = l_Lean_stringToMessageData(v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object* v_declName_1259_, uint8_t v_kind_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
lean_inc(v_declName_1259_);
v___x_1266_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_declName_1259_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = 0;
v___x_1269_ = l_Lean_ConstantInfo_value_x3f(v_a_1267_, v___x_1268_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_declName_1259_);
v___x_1270_ = lean_obj_once(&l_Lean_Meta_addUnificationHint___lam__0___closed__1, &l_Lean_Meta_addUnificationHint___lam__0___closed__1_once, _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1);
v___x_1271_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_1270_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1271_;
}
else
{
lean_object* v_val_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_val_1272_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_val_1272_);
lean_dec_ref(v___x_1269_);
v___x_1273_ = lean_box(0);
v___x_1274_ = l_Lean_Meta_lambdaMetaTelescope(v_val_1272_, v___x_1273_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v_val_1272_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v_snd_1276_; lean_object* v_snd_1277_; lean_object* v___x_1278_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1274_);
v_snd_1276_ = lean_ctor_get(v_a_1275_, 1);
lean_inc(v_snd_1276_);
lean_dec(v_a_1275_);
v_snd_1277_ = lean_ctor_get(v_snd_1276_, 1);
lean_inc(v_snd_1277_);
lean_dec(v_snd_1276_);
v___x_1278_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; 
lean_dec(v_declName_1259_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_a_1279_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v_pattern_1282_; lean_object* v_lhs_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1318_; 
v_a_1281_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1278_);
v_pattern_1282_ = lean_ctor_get(v_a_1281_, 0);
lean_inc_ref(v_pattern_1282_);
v_lhs_1283_ = lean_ctor_get(v_pattern_1282_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_pattern_1282_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v_pattern_1282_, 1);
lean_dec(v_unused_1319_);
v___x_1285_ = v_pattern_1282_;
v_isShared_1286_ = v_isSharedCheck_1318_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_lhs_1283_);
lean_dec(v_pattern_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1318_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v_config_1288_; uint8_t v_trackZetaDelta_1289_; lean_object* v_zetaDeltaSet_1290_; lean_object* v_lctx_1291_; lean_object* v_localInstances_1292_; lean_object* v_defEqCtx_x3f_1293_; lean_object* v_synthPendingDepth_1294_; lean_object* v_canUnfold_x3f_1295_; uint8_t v_univApprox_1296_; uint8_t v_inTypeClassResolution_1297_; uint8_t v_cacheInferType_1298_; uint64_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1287_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_1288_ = lean_ctor_get(v___x_1287_, 0);
v_trackZetaDelta_1289_ = lean_ctor_get_uint8(v___y_1261_, sizeof(void*)*7);
v_zetaDeltaSet_1290_ = lean_ctor_get(v___y_1261_, 1);
v_lctx_1291_ = lean_ctor_get(v___y_1261_, 2);
v_localInstances_1292_ = lean_ctor_get(v___y_1261_, 3);
v_defEqCtx_x3f_1293_ = lean_ctor_get(v___y_1261_, 4);
v_synthPendingDepth_1294_ = lean_ctor_get(v___y_1261_, 5);
v_canUnfold_x3f_1295_ = lean_ctor_get(v___y_1261_, 6);
v_univApprox_1296_ = lean_ctor_get_uint8(v___y_1261_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1297_ = lean_ctor_get_uint8(v___y_1261_, sizeof(void*)*7 + 2);
v_cacheInferType_1298_ = lean_ctor_get_uint8(v___y_1261_, sizeof(void*)*7 + 3);
v___x_1299_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1288_);
lean_inc_ref(v_config_1288_);
v___x_1300_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1300_, 0, v_config_1288_);
lean_ctor_set_uint64(v___x_1300_, sizeof(void*)*1, v___x_1299_);
lean_inc(v_canUnfold_x3f_1295_);
lean_inc(v_synthPendingDepth_1294_);
lean_inc(v_defEqCtx_x3f_1293_);
lean_inc_ref(v_localInstances_1292_);
lean_inc_ref(v_lctx_1291_);
lean_inc(v_zetaDeltaSet_1290_);
v___x_1301_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v_zetaDeltaSet_1290_);
lean_ctor_set(v___x_1301_, 2, v_lctx_1291_);
lean_ctor_set(v___x_1301_, 3, v_localInstances_1292_);
lean_ctor_set(v___x_1301_, 4, v_defEqCtx_x3f_1293_);
lean_ctor_set(v___x_1301_, 5, v_synthPendingDepth_1294_);
lean_ctor_set(v___x_1301_, 6, v_canUnfold_x3f_1295_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*7, v_trackZetaDelta_1289_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*7 + 1, v_univApprox_1296_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1297_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*7 + 3, v_cacheInferType_1298_);
v___x_1302_ = l_Lean_Meta_DiscrTree_mkPath(v_lhs_1283_, v___x_1268_, v___x_1301_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec_ref(v___x_1301_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_a_1281_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
lean_dec_ref(v___x_1304_);
v___x_1305_ = l_Lean_Meta_unificationHintExtension;
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v_declName_1259_);
lean_ctor_set(v___x_1285_, 0, v_a_1303_);
v___x_1307_ = v___x_1285_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_declName_1259_);
v___x_1307_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v___x_1305_, v___x_1307_, v_kind_1260_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1308_;
}
}
else
{
lean_dec(v_a_1303_);
lean_del_object(v___x_1285_);
lean_dec(v_declName_1259_);
return v___x_1304_;
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_del_object(v___x_1285_);
lean_dec(v_a_1281_);
lean_dec(v_declName_1259_);
v_a_1310_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1302_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1302_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_declName_1259_);
v_a_1320_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1274_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1274_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_declName_1259_);
v_a_1328_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1266_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1266_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object* v_declName_1336_, lean_object* v_kind_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v_kind_boxed_1343_; lean_object* v_res_1344_; 
v_kind_boxed_1343_ = lean_unbox(v_kind_1337_);
v_res_1344_ = l_Lean_Meta_addUnificationHint___lam__0(v_declName_1336_, v_kind_boxed_1343_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* v_declName_1345_, uint8_t v_kind_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v___x_1352_; lean_object* v___f_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1352_ = lean_box(v_kind_1346_);
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1353_, 0, v_declName_1345_);
lean_closure_set(v___f_1353_, 1, v___x_1352_);
v___x_1354_ = 0;
v___x_1355_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v___f_1353_, v___x_1354_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* v_declName_1356_, lean_object* v_kind_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
uint8_t v_kind_boxed_1363_; lean_object* v_res_1364_; 
v_kind_boxed_1363_ = lean_unbox(v_kind_1357_);
v_res_1364_ = l_Lean_Meta_addUnificationHint(v_declName_1356_, v_kind_boxed_1363_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object* v_00_u03b1_1365_, lean_object* v_constName_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_constName_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(v_00_u03b1_1373_, v_constName_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1381_, lean_object* v_ref_1382_, lean_object* v_constName_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1382_, v_constName_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1390_, lean_object* v_ref_1391_, lean_object* v_constName_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(v_00_u03b1_1390_, v_ref_1391_, v_constName_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v_ref_1391_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_1399_, lean_object* v_ref_1400_, lean_object* v_msg_1401_, lean_object* v_declHint_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1400_, v_msg_1401_, v_declHint_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_ref_1410_, lean_object* v_msg_1411_, lean_object* v_declHint_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(v_00_u03b1_1409_, v_ref_1410_, v_msg_1411_, v_declHint_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v_ref_1410_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1419_, lean_object* v_declHint_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1419_, v_declHint_1420_, v___y_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1427_, lean_object* v_declHint_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(v_msg_1427_, v_declHint_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1435_, lean_object* v_ref_1436_, lean_object* v_msg_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1436_, v_msg_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_ref_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(v_00_u03b1_1444_, v_ref_1445_, v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v_ref_1445_);
return v_res_1452_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1459_; uint64_t v___x_1460_; 
v___x_1459_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1462_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1463_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set_uint64(v___x_1463_, sizeof(void*)*1, v___x_1461_);
return v___x_1463_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1464_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1468_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
lean_ctor_set(v___x_1468_, 2, v___x_1467_);
lean_ctor_set(v___x_1468_, 3, v___x_1467_);
lean_ctor_set(v___x_1468_, 4, v___x_1467_);
lean_ctor_set(v___x_1468_, 5, v___x_1467_);
return v___x_1468_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
lean_ctor_set(v___x_1470_, 2, v___x_1469_);
lean_ctor_set(v___x_1470_, 3, v___x_1469_);
lean_ctor_set(v___x_1470_, 4, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1471_, lean_object* v___x_1472_, lean_object* v_declName_1473_, lean_object* v_stx_1474_, uint8_t v_kind_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1474_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1479_) == 0)
{
uint8_t v___x_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref(v___x_1479_);
v___x_1480_ = 0;
v___x_1481_ = 1;
v___x_1482_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1483_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1484_ = lean_unsigned_to_nat(32u);
v___x_1485_ = lean_mk_empty_array_with_capacity(v___x_1484_);
v___x_1486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1487_ = ((size_t)5ULL);
lean_inc_n(v___x_1471_, 6);
v___x_1488_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1485_);
lean_ctor_set(v___x_1488_, 2, v___x_1471_);
lean_ctor_set(v___x_1488_, 3, v___x_1471_);
lean_ctor_set_usize(v___x_1488_, 4, v___x_1487_);
v___x_1489_ = lean_box(1);
lean_inc_ref(v___x_1488_);
v___x_1490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1483_);
lean_ctor_set(v___x_1490_, 1, v___x_1488_);
lean_ctor_set(v___x_1490_, 2, v___x_1489_);
v___x_1491_ = lean_mk_empty_array_with_capacity(v___x_1471_);
v___x_1492_ = lean_box(0);
lean_inc(v___x_1472_);
v___x_1493_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1493_, 0, v___x_1482_);
lean_ctor_set(v___x_1493_, 1, v___x_1472_);
lean_ctor_set(v___x_1493_, 2, v___x_1490_);
lean_ctor_set(v___x_1493_, 3, v___x_1491_);
lean_ctor_set(v___x_1493_, 4, v___x_1492_);
lean_ctor_set(v___x_1493_, 5, v___x_1471_);
lean_ctor_set(v___x_1493_, 6, v___x_1492_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*7, v___x_1480_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*7 + 1, v___x_1480_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*7 + 2, v___x_1480_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*7 + 3, v___x_1481_);
v___x_1494_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1471_);
lean_ctor_set(v___x_1494_, 1, v___x_1471_);
lean_ctor_set(v___x_1494_, 2, v___x_1471_);
lean_ctor_set(v___x_1494_, 3, v___x_1471_);
lean_ctor_set(v___x_1494_, 4, v___x_1483_);
lean_ctor_set(v___x_1494_, 5, v___x_1483_);
lean_ctor_set(v___x_1494_, 6, v___x_1483_);
lean_ctor_set(v___x_1494_, 7, v___x_1483_);
lean_ctor_set(v___x_1494_, 8, v___x_1483_);
lean_ctor_set(v___x_1494_, 9, v___x_1483_);
v___x_1495_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1496_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1494_);
lean_ctor_set(v___x_1497_, 1, v___x_1495_);
lean_ctor_set(v___x_1497_, 2, v___x_1472_);
lean_ctor_set(v___x_1497_, 3, v___x_1488_);
lean_ctor_set(v___x_1497_, 4, v___x_1496_);
v___x_1498_ = lean_st_mk_ref(v___x_1497_);
v___x_1499_ = l_Lean_Meta_addUnificationHint(v_declName_1473_, v_kind_1475_, v___x_1493_, v___x_1498_, v___y_1476_, v___y_1477_);
lean_dec_ref(v___x_1493_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1508_; 
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v___x_1499_, 0);
lean_dec(v_unused_1509_);
v___x_1501_ = v___x_1499_;
v_isShared_1502_ = v_isSharedCheck_1508_;
goto v_resetjp_1500_;
}
else
{
lean_dec(v___x_1499_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1508_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1503_ = lean_st_ref_get(v___x_1498_);
lean_dec(v___x_1498_);
lean_dec(v___x_1503_);
v___x_1504_ = lean_box(0);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1504_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_dec(v___x_1498_);
return v___x_1499_;
}
}
else
{
lean_dec(v_declName_1473_);
lean_dec(v___x_1472_);
lean_dec(v___x_1471_);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1510_, lean_object* v___x_1511_, lean_object* v_declName_1512_, lean_object* v_stx_1513_, lean_object* v_kind_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v_kind_boxed_1518_; lean_object* v_res_1519_; 
v_kind_boxed_1518_ = lean_unbox(v_kind_1514_);
v_res_1519_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1510_, v___x_1511_, v_declName_1512_, v_stx_1513_, v_kind_boxed_1518_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v_env_1525_; lean_object* v_options_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1524_ = lean_st_ref_get(v___y_1522_);
v_env_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc_ref(v_env_1525_);
lean_dec(v___x_1524_);
v_options_1526_ = lean_ctor_get(v___y_1521_, 2);
v___x_1527_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1528_ = lean_unsigned_to_nat(32u);
v___x_1529_ = lean_mk_empty_array_with_capacity(v___x_1528_);
lean_dec_ref(v___x_1529_);
v___x_1530_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_1526_);
v___x_1531_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1531_, 0, v_env_1525_);
lean_ctor_set(v___x_1531_, 1, v___x_1527_);
lean_ctor_set(v___x_1531_, 2, v___x_1530_);
lean_ctor_set(v___x_1531_, 3, v_options_1526_);
v___x_1532_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v_msgData_1520_);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_ref_1543_; lean_object* v___x_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1553_; 
v_ref_1543_ = lean_ctor_get(v___y_1540_, 5);
v___x_1544_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msg_1539_, v___y_1540_, v___y_1541_);
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_inc(v_ref_1543_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_ref_1543_);
lean_ctor_set(v___x_1549_, 1, v_a_1545_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 1);
lean_ctor_set(v___x_1547_, 0, v___x_1549_);
v___x_1551_ = v___x_1547_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1558_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1564_ = l_Lean_stringToMessageData(v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1565_, lean_object* v_decl_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1570_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1571_ = l_Lean_MessageData_ofName(v___x_1565_);
v___x_1572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v___x_1574_, v___y_1567_, v___y_1568_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1576_, lean_object* v_decl_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1576_, v_decl_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v_decl_1577_);
return v_res_1581_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = lean_unsigned_to_nat(3033092106u);
v___x_1626_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1627_ = l_Lean_Name_num___override(v___x_1626_, v___x_1625_);
return v___x_1627_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1630_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1631_ = l_Lean_Name_str___override(v___x_1630_, v___x_1629_);
return v___x_1631_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1634_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1635_ = l_Lean_Name_str___override(v___x_1634_, v___x_1633_);
return v___x_1635_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = lean_unsigned_to_nat(2u);
v___x_1637_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1638_ = l_Lean_Name_num___override(v___x_1637_, v___x_1636_);
return v___x_1638_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1645_ = 0;
v___x_1646_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1647_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1648_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1649_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v___x_1647_);
lean_ctor_set(v___x_1649_, 2, v___x_1646_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*3, v___x_1645_);
return v___x_1649_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1650_; lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___f_1650_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___f_1651_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___f_1651_);
lean_ctor_set(v___x_1653_, 2, v___f_1650_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1656_ = l_Lean_registerBuiltinAttribute(v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1659_, lean_object* v_msg_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1660_, v___y_1661_, v___y_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1665_, lean_object* v_msg_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(v_00_u03b1_1665_, v_msg_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1670_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0(void){
_start:
{
uint8_t v___x_1671_; uint64_t v___x_1672_; 
v___x_1671_ = 2;
v___x_1672_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* v_p_1673_, lean_object* v_e_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1680_; uint8_t v_foApprox_1681_; uint8_t v_ctxApprox_1682_; uint8_t v_quasiPatternApprox_1683_; uint8_t v_constApprox_1684_; uint8_t v_isDefEqStuckEx_1685_; uint8_t v_unificationHints_1686_; uint8_t v_proofIrrelevance_1687_; uint8_t v_assignSyntheticOpaque_1688_; uint8_t v_offsetCnstrs_1689_; uint8_t v_etaStruct_1690_; uint8_t v_univApprox_1691_; uint8_t v_iota_1692_; uint8_t v_beta_1693_; uint8_t v_proj_1694_; uint8_t v_zeta_1695_; uint8_t v_zetaDelta_1696_; uint8_t v_zetaUnused_1697_; uint8_t v_zetaHave_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1725_; 
v___x_1680_ = l_Lean_Meta_Context_config(v_a_1675_);
v_foApprox_1681_ = lean_ctor_get_uint8(v___x_1680_, 0);
v_ctxApprox_1682_ = lean_ctor_get_uint8(v___x_1680_, 1);
v_quasiPatternApprox_1683_ = lean_ctor_get_uint8(v___x_1680_, 2);
v_constApprox_1684_ = lean_ctor_get_uint8(v___x_1680_, 3);
v_isDefEqStuckEx_1685_ = lean_ctor_get_uint8(v___x_1680_, 4);
v_unificationHints_1686_ = lean_ctor_get_uint8(v___x_1680_, 5);
v_proofIrrelevance_1687_ = lean_ctor_get_uint8(v___x_1680_, 6);
v_assignSyntheticOpaque_1688_ = lean_ctor_get_uint8(v___x_1680_, 7);
v_offsetCnstrs_1689_ = lean_ctor_get_uint8(v___x_1680_, 8);
v_etaStruct_1690_ = lean_ctor_get_uint8(v___x_1680_, 10);
v_univApprox_1691_ = lean_ctor_get_uint8(v___x_1680_, 11);
v_iota_1692_ = lean_ctor_get_uint8(v___x_1680_, 12);
v_beta_1693_ = lean_ctor_get_uint8(v___x_1680_, 13);
v_proj_1694_ = lean_ctor_get_uint8(v___x_1680_, 14);
v_zeta_1695_ = lean_ctor_get_uint8(v___x_1680_, 15);
v_zetaDelta_1696_ = lean_ctor_get_uint8(v___x_1680_, 16);
v_zetaUnused_1697_ = lean_ctor_get_uint8(v___x_1680_, 17);
v_zetaHave_1698_ = lean_ctor_get_uint8(v___x_1680_, 18);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1700_ = v___x_1680_;
v_isShared_1701_ = v_isSharedCheck_1725_;
goto v_resetjp_1699_;
}
else
{
lean_dec(v___x_1680_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1725_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
uint8_t v_trackZetaDelta_1702_; lean_object* v_zetaDeltaSet_1703_; lean_object* v_lctx_1704_; lean_object* v_localInstances_1705_; lean_object* v_defEqCtx_x3f_1706_; lean_object* v_synthPendingDepth_1707_; lean_object* v_canUnfold_x3f_1708_; uint8_t v_univApprox_1709_; uint8_t v_inTypeClassResolution_1710_; uint8_t v_cacheInferType_1711_; uint8_t v___x_1712_; lean_object* v_config_1714_; 
v_trackZetaDelta_1702_ = lean_ctor_get_uint8(v_a_1675_, sizeof(void*)*7);
v_zetaDeltaSet_1703_ = lean_ctor_get(v_a_1675_, 1);
v_lctx_1704_ = lean_ctor_get(v_a_1675_, 2);
v_localInstances_1705_ = lean_ctor_get(v_a_1675_, 3);
v_defEqCtx_x3f_1706_ = lean_ctor_get(v_a_1675_, 4);
v_synthPendingDepth_1707_ = lean_ctor_get(v_a_1675_, 5);
v_canUnfold_x3f_1708_ = lean_ctor_get(v_a_1675_, 6);
v_univApprox_1709_ = lean_ctor_get_uint8(v_a_1675_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1710_ = lean_ctor_get_uint8(v_a_1675_, sizeof(void*)*7 + 2);
v_cacheInferType_1711_ = lean_ctor_get_uint8(v_a_1675_, sizeof(void*)*7 + 3);
v___x_1712_ = 2;
if (v_isShared_1701_ == 0)
{
v_config_1714_ = v___x_1700_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 0, v_foApprox_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 1, v_ctxApprox_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 2, v_quasiPatternApprox_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 3, v_constApprox_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 4, v_isDefEqStuckEx_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 5, v_unificationHints_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 6, v_proofIrrelevance_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 7, v_assignSyntheticOpaque_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 8, v_offsetCnstrs_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 10, v_etaStruct_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 11, v_univApprox_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 12, v_iota_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 13, v_beta_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 14, v_proj_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 15, v_zeta_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 16, v_zetaDelta_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 17, v_zetaUnused_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, 18, v_zetaHave_1698_);
v_config_1714_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
uint64_t v___x_1715_; uint64_t v___x_1716_; uint64_t v___x_1717_; uint64_t v___x_1718_; uint64_t v___x_1719_; uint64_t v_key_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_ctor_set_uint8(v_config_1714_, 9, v___x_1712_);
v___x_1715_ = l_Lean_Meta_Context_configKey(v_a_1675_);
v___x_1716_ = 2ULL;
v___x_1717_ = lean_uint64_shift_right(v___x_1715_, v___x_1716_);
v___x_1718_ = lean_uint64_shift_left(v___x_1717_, v___x_1716_);
v___x_1719_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0);
v_key_1720_ = lean_uint64_lor(v___x_1718_, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1721_, 0, v_config_1714_);
lean_ctor_set_uint64(v___x_1721_, sizeof(void*)*1, v_key_1720_);
lean_inc(v_canUnfold_x3f_1708_);
lean_inc(v_synthPendingDepth_1707_);
lean_inc(v_defEqCtx_x3f_1706_);
lean_inc_ref(v_localInstances_1705_);
lean_inc_ref(v_lctx_1704_);
lean_inc(v_zetaDeltaSet_1703_);
v___x_1722_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v_zetaDeltaSet_1703_);
lean_ctor_set(v___x_1722_, 2, v_lctx_1704_);
lean_ctor_set(v___x_1722_, 3, v_localInstances_1705_);
lean_ctor_set(v___x_1722_, 4, v_defEqCtx_x3f_1706_);
lean_ctor_set(v___x_1722_, 5, v_synthPendingDepth_1707_);
lean_ctor_set(v___x_1722_, 6, v_canUnfold_x3f_1708_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*7, v_trackZetaDelta_1702_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*7 + 1, v_univApprox_1709_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1710_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*7 + 3, v_cacheInferType_1711_);
lean_inc(v_a_1678_);
lean_inc_ref(v_a_1677_);
lean_inc(v_a_1676_);
v___x_1723_ = lean_is_expr_def_eq(v_p_1673_, v_e_1674_, v___x_1722_, v_a_1676_, v_a_1677_, v_a_1678_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object* v_p_1726_, lean_object* v_e_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_p_1726_, v_e_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
if (lean_obj_tag(v_x_1734_) == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = l_List_reverse___redArg(v_x_1735_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
else
{
lean_object* v_tail_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1761_; 
v_tail_1743_ = lean_ctor_get(v_x_1734_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_x_1734_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_x_1734_, 0);
lean_dec(v_unused_1762_);
v___x_1745_ = v_x_1734_;
v_isShared_1746_ = v_isSharedCheck_1761_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_tail_1743_);
lean_dec(v_x_1734_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1761_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___x_1747_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_x_1735_);
lean_ctor_set(v___x_1745_, 0, v_a_1748_);
v___x_1750_ = v___x_1745_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1748_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_x_1735_);
v___x_1750_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
v_x_1734_ = v_tail_1743_;
v_x_1735_ = v___x_1750_;
goto _start;
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_x_1735_);
v_a_1753_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1747_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1747_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v_x_1763_, v_x_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1770_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1771_; double v___x_1772_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_float_of_nat(v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object* v_cls_1776_, lean_object* v_msg_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_ref_1783_; lean_object* v___x_1784_; lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1829_; 
v_ref_1783_ = lean_ctor_get(v___y_1780_, 5);
v___x_1784_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1829_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1829_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v_traceState_1790_; lean_object* v_env_1791_; lean_object* v_nextMacroScope_1792_; lean_object* v_ngen_1793_; lean_object* v_auxDeclNGen_1794_; lean_object* v_cache_1795_; lean_object* v_messages_1796_; lean_object* v_infoState_1797_; lean_object* v_snapshotTasks_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1828_; 
v___x_1789_ = lean_st_ref_take(v___y_1781_);
v_traceState_1790_ = lean_ctor_get(v___x_1789_, 4);
v_env_1791_ = lean_ctor_get(v___x_1789_, 0);
v_nextMacroScope_1792_ = lean_ctor_get(v___x_1789_, 1);
v_ngen_1793_ = lean_ctor_get(v___x_1789_, 2);
v_auxDeclNGen_1794_ = lean_ctor_get(v___x_1789_, 3);
v_cache_1795_ = lean_ctor_get(v___x_1789_, 5);
v_messages_1796_ = lean_ctor_get(v___x_1789_, 6);
v_infoState_1797_ = lean_ctor_get(v___x_1789_, 7);
v_snapshotTasks_1798_ = lean_ctor_get(v___x_1789_, 8);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1800_ = v___x_1789_;
v_isShared_1801_ = v_isSharedCheck_1828_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snapshotTasks_1798_);
lean_inc(v_infoState_1797_);
lean_inc(v_messages_1796_);
lean_inc(v_cache_1795_);
lean_inc(v_traceState_1790_);
lean_inc(v_auxDeclNGen_1794_);
lean_inc(v_ngen_1793_);
lean_inc(v_nextMacroScope_1792_);
lean_inc(v_env_1791_);
lean_dec(v___x_1789_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1828_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
uint64_t v_tid_1802_; lean_object* v_traces_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1827_; 
v_tid_1802_ = lean_ctor_get_uint64(v_traceState_1790_, sizeof(void*)*1);
v_traces_1803_ = lean_ctor_get(v_traceState_1790_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_traceState_1790_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1805_ = v_traceState_1790_;
v_isShared_1806_ = v_isSharedCheck_1827_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_traces_1803_);
lean_dec(v_traceState_1790_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1827_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; double v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
v___x_1809_ = 0;
v___x_1810_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_1811_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1811_, 0, v_cls_1776_);
lean_ctor_set(v___x_1811_, 1, v___x_1807_);
lean_ctor_set(v___x_1811_, 2, v___x_1810_);
lean_ctor_set_float(v___x_1811_, sizeof(void*)*3, v___x_1808_);
lean_ctor_set_float(v___x_1811_, sizeof(void*)*3 + 8, v___x_1808_);
lean_ctor_set_uint8(v___x_1811_, sizeof(void*)*3 + 16, v___x_1809_);
v___x_1812_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2));
v___x_1813_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v_a_1785_);
lean_ctor_set(v___x_1813_, 2, v___x_1812_);
lean_inc(v_ref_1783_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_ref_1783_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l_Lean_PersistentArray_push___redArg(v_traces_1803_, v___x_1814_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1815_);
v___x_1817_ = v___x_1805_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1815_);
lean_ctor_set_uint64(v_reuseFailAlloc_1826_, sizeof(void*)*1, v_tid_1802_);
v___x_1817_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 4, v___x_1817_);
v___x_1819_ = v___x_1800_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_env_1791_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_nextMacroScope_1792_);
lean_ctor_set(v_reuseFailAlloc_1825_, 2, v_ngen_1793_);
lean_ctor_set(v_reuseFailAlloc_1825_, 3, v_auxDeclNGen_1794_);
lean_ctor_set(v_reuseFailAlloc_1825_, 4, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1825_, 5, v_cache_1795_);
lean_ctor_set(v_reuseFailAlloc_1825_, 6, v_messages_1796_);
lean_ctor_set(v_reuseFailAlloc_1825_, 7, v_infoState_1797_);
lean_ctor_set(v_reuseFailAlloc_1825_, 8, v_snapshotTasks_1798_);
v___x_1819_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1820_ = lean_st_ref_set(v___y_1781_, v___x_1819_);
v___x_1821_ = lean_box(0);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1821_);
v___x_1823_ = v___x_1787_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object* v_cls_1830_, lean_object* v_msg_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_1830_, v_msg_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object* v_as_1841_, size_t v_sz_1842_, size_t v_i_1843_, lean_object* v_b_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_a_1851_; uint8_t v___x_1855_; 
v___x_1855_ = lean_usize_dec_lt(v_i_1843_, v_sz_1842_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_b_1844_);
return v___x_1856_;
}
else
{
lean_object* v_snd_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1947_; 
v_snd_1857_ = lean_ctor_get(v_b_1844_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_b_1844_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v_b_1844_, 0);
lean_dec(v_unused_1948_);
v___x_1859_ = v_b_1844_;
v_isShared_1860_ = v_isSharedCheck_1947_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_snd_1857_);
lean_dec(v_b_1844_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1947_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_array_1861_; lean_object* v_start_1862_; lean_object* v_stop_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v_array_1861_ = lean_ctor_get(v_snd_1857_, 0);
v_start_1862_ = lean_ctor_get(v_snd_1857_, 1);
v_stop_1863_ = lean_ctor_get(v_snd_1857_, 2);
v___x_1864_ = lean_box(0);
v___x_1865_ = lean_nat_dec_lt(v_start_1862_, v_stop_1863_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1867_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1864_);
v___x_1867_ = v___x_1859_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_snd_1857_);
v___x_1867_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
return v___x_1868_;
}
}
else
{
lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1943_; 
lean_inc(v_stop_1863_);
lean_inc(v_start_1862_);
lean_inc_ref(v_array_1861_);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_snd_1857_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; lean_object* v_unused_1945_; lean_object* v_unused_1946_; 
v_unused_1944_ = lean_ctor_get(v_snd_1857_, 2);
lean_dec(v_unused_1944_);
v_unused_1945_ = lean_ctor_get(v_snd_1857_, 1);
lean_dec(v_unused_1945_);
v_unused_1946_ = lean_ctor_get(v_snd_1857_, 0);
lean_dec(v_unused_1946_);
v___x_1871_ = v_snd_1857_;
v_isShared_1872_ = v_isSharedCheck_1943_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v_snd_1857_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1943_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1873_ = lean_array_fget(v_array_1861_, v_start_1862_);
v___x_1874_ = lean_unsigned_to_nat(1u);
v___x_1875_ = lean_nat_add(v_start_1862_, v___x_1874_);
lean_dec(v_start_1862_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 1, v___x_1875_);
v___x_1877_ = v___x_1871_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_array_1861_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_stop_1863_);
v___x_1877_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
uint8_t v___x_1878_; uint8_t v___x_1879_; uint8_t v___x_1880_; 
v___x_1878_ = 3;
v___x_1879_ = lean_unbox(v___x_1873_);
lean_dec(v___x_1873_);
v___x_1880_ = l_Lean_instBEqBinderInfo_beq(v___x_1879_, v___x_1878_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1882_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1877_);
lean_ctor_set(v___x_1859_, 0, v___x_1864_);
v___x_1882_ = v___x_1859_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
v_a_1851_ = v___x_1882_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1885_; 
v_a_1884_ = lean_array_uget_borrowed(v_as_1841_, v_i_1843_);
lean_inc(v___y_1848_);
lean_inc_ref(v___y_1847_);
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v_a_1884_);
v___x_1885_ = lean_infer_type(v_a_1884_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = l_Lean_Meta_trySynthInstance(v_a_1886_, v___x_1864_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1925_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1925_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1925_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
if (lean_obj_tag(v_a_1888_) == 1)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; 
lean_del_object(v___x_1890_);
v_a_1892_ = lean_ctor_get(v_a_1888_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v_a_1888_);
lean_inc(v_a_1884_);
v___x_1893_ = l_Lean_Meta_isExprDefEq(v_a_1884_, v_a_1892_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1909_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1909_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1909_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_unbox(v_a_1894_);
lean_dec(v_a_1894_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1877_);
lean_ctor_set(v___x_1859_, 0, v___x_1899_);
v___x_1901_ = v___x_1859_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1877_);
v___x_1901_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1903_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1901_);
v___x_1903_ = v___x_1896_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_object* v___x_1907_; 
lean_del_object(v___x_1896_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1877_);
lean_ctor_set(v___x_1859_, 0, v___x_1864_);
v___x_1907_ = v___x_1859_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v___x_1877_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v_a_1851_ = v___x_1907_;
goto v___jp_1850_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v___x_1877_);
lean_del_object(v___x_1859_);
v_a_1910_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1893_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1893_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
lean_dec(v_a_1888_);
v___x_1918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1877_);
lean_ctor_set(v___x_1859_, 0, v___x_1918_);
v___x_1920_ = v___x_1859_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1877_);
v___x_1920_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1922_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1920_);
v___x_1922_ = v___x_1890_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref(v___x_1877_);
lean_del_object(v___x_1859_);
v_a_1926_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1887_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1887_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref(v___x_1877_);
lean_del_object(v___x_1859_);
v_a_1934_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1885_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1885_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
}
}
}
}
v___jp_1850_:
{
size_t v___x_1852_; size_t v___x_1853_; 
v___x_1852_ = ((size_t)1ULL);
v___x_1853_ = lean_usize_add(v_i_1843_, v___x_1852_);
v_i_1843_ = v___x_1853_;
v_b_1844_ = v_a_1851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object* v_as_1949_, lean_object* v_sz_1950_, lean_object* v_i_1951_, lean_object* v_b_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
size_t v_sz_boxed_1958_; size_t v_i_boxed_1959_; lean_object* v_res_1960_; 
v_sz_boxed_1958_ = lean_unbox_usize(v_sz_1950_);
lean_dec(v_sz_1950_);
v_i_boxed_1959_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_res_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_as_1949_, v_sz_boxed_1958_, v_i_boxed_1959_, v_b_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec_ref(v_as_1949_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object* v_as_x27_1964_, lean_object* v_b_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
if (lean_obj_tag(v_as_x27_1964_) == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_b_1965_);
return v___x_1971_;
}
else
{
lean_object* v_head_1972_; lean_object* v_tail_1973_; lean_object* v_lhs_1974_; lean_object* v_rhs_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v_b_1965_);
v_head_1972_ = lean_ctor_get(v_as_x27_1964_, 0);
lean_inc(v_head_1972_);
v_tail_1973_ = lean_ctor_get(v_as_x27_1964_, 1);
lean_inc(v_tail_1973_);
lean_dec_ref(v_as_x27_1964_);
v_lhs_1974_ = lean_ctor_get(v_head_1972_, 0);
v_rhs_1975_ = lean_ctor_get(v_head_1972_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_head_1972_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1977_ = v_head_1972_;
v_isShared_1978_ = v_isSharedCheck_2004_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_rhs_1975_);
lean_inc(v_lhs_1974_);
lean_dec(v_head_1972_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2004_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; 
lean_inc(v___y_1969_);
lean_inc_ref(v___y_1968_);
lean_inc(v___y_1967_);
lean_inc_ref(v___y_1966_);
v___x_1979_ = lean_is_expr_def_eq(v_lhs_1974_, v_rhs_1975_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1995_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1995_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1995_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_unbox(v_a_1980_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_dec(v_tail_1973_);
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v_a_1980_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 1, v___x_1984_);
lean_ctor_set(v___x_1977_, 0, v___x_1986_);
v___x_1988_ = v___x_1977_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___x_1984_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1988_);
v___x_1990_ = v___x_1982_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
else
{
lean_object* v___x_1993_; 
lean_del_object(v___x_1982_);
lean_dec(v_a_1980_);
lean_del_object(v___x_1977_);
v___x_1993_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_as_x27_1964_ = v_tail_1973_;
v_b_1965_ = v___x_1993_;
goto _start;
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_del_object(v___x_1977_);
lean_dec(v_tail_1973_);
v_a_1996_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1979_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1979_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object* v_as_x27_2005_, lean_object* v_b_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2005_, v_b_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2012_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2013_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0);
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8(void){
_start:
{
lean_object* v_cls_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_cls_2028_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2029_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7));
v___x_2030_ = l_Lean_Name_append(v___x_2029_, v_cls_2028_);
return v___x_2030_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object* v_candidate_2034_, lean_object* v_t_2035_, lean_object* v_s_2036_, uint8_t v_mayPostpone_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Meta_saveState___redArg(v_a_2039_, v_a_2041_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2294_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2294_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2294_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___y_2049_; uint8_t v___y_2050_; lean_object* v_a_2072_; uint8_t v_a_2076_; lean_object* v___x_2088_; lean_object* v_cache_2089_; lean_object* v_mctx_2090_; lean_object* v_zetaDeltaFVarIds_2091_; lean_object* v_postponed_2092_; lean_object* v_diag_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2293_; 
v___x_2088_ = lean_st_ref_take(v_a_2039_);
v_cache_2089_ = lean_ctor_get(v___x_2088_, 1);
v_mctx_2090_ = lean_ctor_get(v___x_2088_, 0);
v_zetaDeltaFVarIds_2091_ = lean_ctor_get(v___x_2088_, 2);
v_postponed_2092_ = lean_ctor_get(v___x_2088_, 3);
v_diag_2093_ = lean_ctor_get(v___x_2088_, 4);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2095_ = v___x_2088_;
v_isShared_2096_ = v_isSharedCheck_2293_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_diag_2093_);
lean_inc(v_postponed_2092_);
lean_inc(v_zetaDeltaFVarIds_2091_);
lean_inc(v_cache_2089_);
lean_inc(v_mctx_2090_);
lean_dec(v___x_2088_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2293_;
goto v_resetjp_2094_;
}
v___jp_2048_:
{
if (v___y_2050_ == 0)
{
lean_object* v___x_2051_; 
lean_del_object(v___x_2046_);
v___x_2051_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2044_, v_a_2039_, v_a_2041_);
lean_dec(v_a_2044_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v___x_2051_, 0);
lean_dec(v_unused_2059_);
v___x_2053_ = v___x_2051_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v___x_2051_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set_tag(v___x_2053_, 1);
lean_ctor_set(v___x_2053_, 0, v___y_2049_);
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___y_2049_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v___y_2049_);
v_a_2060_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2051_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2051_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v___x_2069_; 
lean_dec(v_a_2044_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 1);
lean_ctor_set(v___x_2046_, 0, v___y_2049_);
v___x_2069_ = v___x_2046_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___y_2049_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
v___jp_2071_:
{
uint8_t v___x_2073_; 
v___x_2073_ = l_Lean_Exception_isInterrupt(v_a_2072_);
if (v___x_2073_ == 0)
{
uint8_t v___x_2074_; 
lean_inc_ref(v_a_2072_);
v___x_2074_ = l_Lean_Exception_isRuntime(v_a_2072_);
v___y_2049_ = v_a_2072_;
v___y_2050_ = v___x_2074_;
goto v___jp_2048_;
}
else
{
v___y_2049_ = v_a_2072_;
v___y_2050_ = v___x_2073_;
goto v___jp_2048_;
}
}
v___jp_2075_:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2044_, v_a_2039_, v_a_2041_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2085_; 
lean_del_object(v___x_2046_);
lean_dec(v_a_2044_);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2077_, 0);
lean_dec(v_unused_2086_);
v___x_2079_ = v___x_2077_;
v_isShared_2080_ = v_isSharedCheck_2085_;
goto v_resetjp_2078_;
}
else
{
lean_dec(v___x_2077_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2085_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_box(v_a_2076_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2081_);
v___x_2083_ = v___x_2079_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_object* v_a_2087_; 
v_a_2087_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v___x_2077_);
v_a_2072_ = v_a_2087_;
goto v___jp_2071_;
}
}
v_resetjp_2094_:
{
lean_object* v_inferType_2097_; lean_object* v_funInfo_2098_; lean_object* v_synthInstance_2099_; lean_object* v_whnf_2100_; lean_object* v_defEqPerm_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2291_; 
v_inferType_2097_ = lean_ctor_get(v_cache_2089_, 0);
v_funInfo_2098_ = lean_ctor_get(v_cache_2089_, 1);
v_synthInstance_2099_ = lean_ctor_get(v_cache_2089_, 2);
v_whnf_2100_ = lean_ctor_get(v_cache_2089_, 3);
v_defEqPerm_2101_ = lean_ctor_get(v_cache_2089_, 5);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_cache_2089_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v_cache_2089_, 4);
lean_dec(v_unused_2292_);
v___x_2103_ = v_cache_2089_;
v_isShared_2104_ = v_isSharedCheck_2291_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_defEqPerm_2101_);
lean_inc(v_whnf_2100_);
lean_inc(v_synthInstance_2099_);
lean_inc(v_funInfo_2098_);
lean_inc(v_inferType_2097_);
lean_dec(v_cache_2089_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2291_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v___x_2105_);
v___x_2107_ = v___x_2103_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_inferType_2097_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_funInfo_2098_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_synthInstance_2099_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_whnf_2100_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2290_, 5, v_defEqPerm_2101_);
v___x_2107_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 1, v___x_2107_);
v___x_2109_ = v___x_2095_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_mctx_2090_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2289_, 2, v_zetaDeltaFVarIds_2091_);
lean_ctor_set(v_reuseFailAlloc_2289_, 3, v_postponed_2092_);
lean_ctor_set(v_reuseFailAlloc_2289_, 4, v_diag_2093_);
v___x_2109_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_st_ref_set(v_a_2039_, v___x_2109_);
v___x_2111_ = l_Lean_Meta_getResetPostponed___redArg(v_a_2039_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; uint8_t v_a_2114_; lean_object* v___x_2155_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___x_2111_);
lean_inc(v_candidate_2034_);
v___x_2155_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_candidate_2034_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = l_Lean_ConstantInfo_levelParams(v_a_2156_);
v___x_2158_ = lean_box(0);
v___x_2159_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v___x_2157_, v___x_2158_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = 0;
v___x_2162_ = l_Lean_Core_instantiateValueLevelParams(v_a_2156_, v_a_2160_, v___x_2161_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2156_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___x_2162_);
v___x_2164_ = lean_box(0);
v___x_2165_ = l_Lean_Meta_lambdaMetaTelescope(v_a_2163_, v___x_2164_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2163_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v_snd_2167_; lean_object* v_fst_2168_; lean_object* v_fst_2169_; lean_object* v_snd_2170_; lean_object* v___x_2171_; uint8_t v_foApprox_2172_; uint8_t v_ctxApprox_2173_; uint8_t v_quasiPatternApprox_2174_; uint8_t v_constApprox_2175_; uint8_t v_isDefEqStuckEx_2176_; uint8_t v_proofIrrelevance_2177_; uint8_t v_assignSyntheticOpaque_2178_; uint8_t v_offsetCnstrs_2179_; uint8_t v_transparency_2180_; uint8_t v_etaStruct_2181_; uint8_t v_univApprox_2182_; uint8_t v_iota_2183_; uint8_t v_beta_2184_; uint8_t v_proj_2185_; uint8_t v_zeta_2186_; uint8_t v_zetaDelta_2187_; uint8_t v_zetaUnused_2188_; uint8_t v_zetaHave_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2276_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref(v___x_2165_);
v_snd_2167_ = lean_ctor_get(v_a_2166_, 1);
lean_inc(v_snd_2167_);
v_fst_2168_ = lean_ctor_get(v_a_2166_, 0);
lean_inc(v_fst_2168_);
lean_dec(v_a_2166_);
v_fst_2169_ = lean_ctor_get(v_snd_2167_, 0);
lean_inc(v_fst_2169_);
v_snd_2170_ = lean_ctor_get(v_snd_2167_, 1);
lean_inc(v_snd_2170_);
lean_dec(v_snd_2167_);
v___x_2171_ = l_Lean_Meta_Context_config(v_a_2038_);
v_foApprox_2172_ = lean_ctor_get_uint8(v___x_2171_, 0);
v_ctxApprox_2173_ = lean_ctor_get_uint8(v___x_2171_, 1);
v_quasiPatternApprox_2174_ = lean_ctor_get_uint8(v___x_2171_, 2);
v_constApprox_2175_ = lean_ctor_get_uint8(v___x_2171_, 3);
v_isDefEqStuckEx_2176_ = lean_ctor_get_uint8(v___x_2171_, 4);
v_proofIrrelevance_2177_ = lean_ctor_get_uint8(v___x_2171_, 6);
v_assignSyntheticOpaque_2178_ = lean_ctor_get_uint8(v___x_2171_, 7);
v_offsetCnstrs_2179_ = lean_ctor_get_uint8(v___x_2171_, 8);
v_transparency_2180_ = lean_ctor_get_uint8(v___x_2171_, 9);
v_etaStruct_2181_ = lean_ctor_get_uint8(v___x_2171_, 10);
v_univApprox_2182_ = lean_ctor_get_uint8(v___x_2171_, 11);
v_iota_2183_ = lean_ctor_get_uint8(v___x_2171_, 12);
v_beta_2184_ = lean_ctor_get_uint8(v___x_2171_, 13);
v_proj_2185_ = lean_ctor_get_uint8(v___x_2171_, 14);
v_zeta_2186_ = lean_ctor_get_uint8(v___x_2171_, 15);
v_zetaDelta_2187_ = lean_ctor_get_uint8(v___x_2171_, 16);
v_zetaUnused_2188_ = lean_ctor_get_uint8(v___x_2171_, 17);
v_zetaHave_2189_ = lean_ctor_get_uint8(v___x_2171_, 18);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2191_ = v___x_2171_;
v_isShared_2192_ = v_isSharedCheck_2276_;
goto v_resetjp_2190_;
}
else
{
lean_dec(v___x_2171_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2276_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; 
v___x_2193_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_2170_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_dec_ref(v___x_2193_);
lean_del_object(v___x_2191_);
lean_dec(v_fst_2169_);
lean_dec(v_fst_2168_);
lean_dec(v_a_2112_);
lean_dec_ref(v_s_2036_);
lean_dec_ref(v_t_2035_);
lean_dec(v_candidate_2034_);
v_a_2076_ = v___x_2161_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2194_; uint8_t v_trackZetaDelta_2195_; lean_object* v_zetaDeltaSet_2196_; lean_object* v_lctx_2197_; lean_object* v_localInstances_2198_; lean_object* v_defEqCtx_x3f_2199_; lean_object* v_synthPendingDepth_2200_; lean_object* v_canUnfold_x3f_2201_; uint8_t v_univApprox_2202_; uint8_t v_inTypeClassResolution_2203_; uint8_t v_cacheInferType_2204_; lean_object* v_pattern_2205_; lean_object* v_constraints_2206_; uint8_t v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v_lhs_2239_; lean_object* v_rhs_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2275_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v___x_2193_);
v_trackZetaDelta_2195_ = lean_ctor_get_uint8(v_a_2038_, sizeof(void*)*7);
v_zetaDeltaSet_2196_ = lean_ctor_get(v_a_2038_, 1);
v_lctx_2197_ = lean_ctor_get(v_a_2038_, 2);
v_localInstances_2198_ = lean_ctor_get(v_a_2038_, 3);
v_defEqCtx_x3f_2199_ = lean_ctor_get(v_a_2038_, 4);
v_synthPendingDepth_2200_ = lean_ctor_get(v_a_2038_, 5);
v_canUnfold_x3f_2201_ = lean_ctor_get(v_a_2038_, 6);
v_univApprox_2202_ = lean_ctor_get_uint8(v_a_2038_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2203_ = lean_ctor_get_uint8(v_a_2038_, sizeof(void*)*7 + 2);
v_cacheInferType_2204_ = lean_ctor_get_uint8(v_a_2038_, sizeof(void*)*7 + 3);
v_pattern_2205_ = lean_ctor_get(v_a_2194_, 0);
lean_inc_ref(v_pattern_2205_);
v_constraints_2206_ = lean_ctor_get(v_a_2194_, 1);
lean_inc(v_constraints_2206_);
lean_dec(v_a_2194_);
v_lhs_2239_ = lean_ctor_get(v_pattern_2205_, 0);
v_rhs_2240_ = lean_ctor_get(v_pattern_2205_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_pattern_2205_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2242_ = v_pattern_2205_;
v_isShared_2243_ = v_isSharedCheck_2275_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_rhs_2240_);
lean_inc(v_lhs_2239_);
lean_dec(v_pattern_2205_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2275_;
goto v_resetjp_2241_;
}
v___jp_2207_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2214_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_constraints_2206_, v___x_2213_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v_fst_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2236_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref(v___x_2214_);
v_fst_2216_ = lean_ctor_get(v_a_2215_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_a_2215_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; 
v_unused_2237_ = lean_ctor_get(v_a_2215_, 1);
lean_dec(v_unused_2237_);
v___x_2218_ = v_a_2215_;
v_isShared_2219_ = v_isSharedCheck_2236_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_fst_2216_);
lean_dec(v_a_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2236_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
if (lean_obj_tag(v_fst_2216_) == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = lean_array_get_size(v_fst_2169_);
v___x_2222_ = l_Array_toSubarray___redArg(v_fst_2169_, v___x_2220_, v___x_2221_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2222_);
lean_ctor_set(v___x_2218_, 0, v___x_2164_);
v___x_2224_ = v___x_2218_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; 
v_sz_2225_ = lean_array_size(v_fst_2168_);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_fst_2168_, v_sz_2225_, v___x_2226_, v___x_2224_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v_fst_2168_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v_fst_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2227_);
v_fst_2229_ = lean_ctor_get(v_a_2228_, 0);
lean_inc(v_fst_2229_);
lean_dec(v_a_2228_);
if (lean_obj_tag(v_fst_2229_) == 0)
{
v_a_2114_ = v___y_2208_;
goto v___jp_2113_;
}
else
{
lean_object* v_val_2230_; uint8_t v___x_2231_; 
v_val_2230_ = lean_ctor_get(v_fst_2229_, 0);
lean_inc(v_val_2230_);
lean_dec_ref(v_fst_2229_);
v___x_2231_ = lean_unbox(v_val_2230_);
lean_dec(v_val_2230_);
v_a_2114_ = v___x_2231_;
goto v___jp_2113_;
}
}
else
{
lean_object* v_a_2232_; 
lean_dec(v_a_2112_);
v_a_2232_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2232_);
lean_dec_ref(v___x_2227_);
v_a_2072_ = v_a_2232_;
goto v___jp_2071_;
}
}
}
else
{
lean_object* v_val_2234_; uint8_t v___x_2235_; 
lean_del_object(v___x_2218_);
lean_dec(v_fst_2169_);
lean_dec(v_fst_2168_);
v_val_2234_ = lean_ctor_get(v_fst_2216_, 0);
lean_inc(v_val_2234_);
lean_dec_ref(v_fst_2216_);
v___x_2235_ = lean_unbox(v_val_2234_);
lean_dec(v_val_2234_);
v_a_2114_ = v___x_2235_;
goto v___jp_2113_;
}
}
}
else
{
lean_object* v_a_2238_; 
lean_dec(v_fst_2169_);
lean_dec(v_fst_2168_);
lean_dec(v_a_2112_);
v_a_2238_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v___x_2214_);
v_a_2072_ = v_a_2238_;
goto v___jp_2071_;
}
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2192_ == 0)
{
v___x_2245_ = v___x_2191_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 0, v_foApprox_2172_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 1, v_ctxApprox_2173_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 2, v_quasiPatternApprox_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 3, v_constApprox_2175_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 4, v_isDefEqStuckEx_2176_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 6, v_proofIrrelevance_2177_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 7, v_assignSyntheticOpaque_2178_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 8, v_offsetCnstrs_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 9, v_transparency_2180_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 10, v_etaStruct_2181_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 11, v_univApprox_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 12, v_iota_2183_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 13, v_beta_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 14, v_proj_2185_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 15, v_zeta_2186_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 16, v_zetaDelta_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 17, v_zetaUnused_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, 18, v_zetaHave_2189_);
v___x_2245_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
uint64_t v___x_2246_; lean_object* v_cls_2247_; lean_object* v___y_2249_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_ctor_set_uint8(v___x_2245_, 5, v___x_2161_);
v___x_2246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2245_);
v_cls_2247_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2268_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2268_, 0, v___x_2245_);
lean_ctor_set_uint64(v___x_2268_, sizeof(void*)*1, v___x_2246_);
lean_inc(v_canUnfold_x3f_2201_);
lean_inc(v_synthPendingDepth_2200_);
lean_inc(v_defEqCtx_x3f_2199_);
lean_inc_ref(v_localInstances_2198_);
lean_inc_ref(v_lctx_2197_);
lean_inc(v_zetaDeltaSet_2196_);
v___x_2269_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v_zetaDeltaSet_2196_);
lean_ctor_set(v___x_2269_, 2, v_lctx_2197_);
lean_ctor_set(v___x_2269_, 3, v_localInstances_2198_);
lean_ctor_set(v___x_2269_, 4, v_defEqCtx_x3f_2199_);
lean_ctor_set(v___x_2269_, 5, v_synthPendingDepth_2200_);
lean_ctor_set(v___x_2269_, 6, v_canUnfold_x3f_2201_);
lean_ctor_set_uint8(v___x_2269_, sizeof(void*)*7, v_trackZetaDelta_2195_);
lean_ctor_set_uint8(v___x_2269_, sizeof(void*)*7 + 1, v_univApprox_2202_);
lean_ctor_set_uint8(v___x_2269_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2203_);
lean_ctor_set_uint8(v___x_2269_, sizeof(void*)*7 + 3, v_cacheInferType_2204_);
v___x_2270_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_lhs_2239_, v_t_2035_, v___x_2269_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; uint8_t v___x_2272_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
v___x_2272_ = lean_unbox(v_a_2271_);
lean_dec(v_a_2271_);
if (v___x_2272_ == 0)
{
lean_dec_ref(v___x_2269_);
lean_dec_ref(v_rhs_2240_);
lean_dec_ref(v_s_2036_);
v___y_2249_ = v___x_2270_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2273_; 
lean_dec_ref(v___x_2270_);
v___x_2273_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_rhs_2240_, v_s_2036_, v___x_2269_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec_ref(v___x_2269_);
v___y_2249_ = v___x_2273_;
goto v___jp_2248_;
}
}
else
{
lean_dec_ref(v___x_2269_);
lean_dec_ref(v_rhs_2240_);
lean_dec_ref(v_s_2036_);
v___y_2249_ = v___x_2270_;
goto v___jp_2248_;
}
v___jp_2248_:
{
if (lean_obj_tag(v___y_2249_) == 0)
{
lean_object* v_a_2250_; uint8_t v___x_2251_; 
v_a_2250_ = lean_ctor_get(v___y_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref(v___y_2249_);
v___x_2251_ = lean_unbox(v_a_2250_);
if (v___x_2251_ == 0)
{
lean_dec(v_a_2250_);
lean_del_object(v___x_2242_);
lean_dec(v_constraints_2206_);
lean_dec(v_fst_2169_);
lean_dec(v_fst_2168_);
lean_dec(v_a_2112_);
lean_dec(v_candidate_2034_);
v_a_2076_ = v___x_2161_;
goto v___jp_2075_;
}
else
{
lean_object* v_options_2252_; uint8_t v_hasTrace_2253_; 
v_options_2252_ = lean_ctor_get(v_a_2040_, 2);
v_hasTrace_2253_ = lean_ctor_get_uint8(v_options_2252_, sizeof(void*)*1);
if (v_hasTrace_2253_ == 0)
{
uint8_t v___x_2254_; 
lean_del_object(v___x_2242_);
lean_dec(v_candidate_2034_);
v___x_2254_ = lean_unbox(v_a_2250_);
lean_dec(v_a_2250_);
v___y_2208_ = v___x_2254_;
v___y_2209_ = v_a_2038_;
v___y_2210_ = v_a_2039_;
v___y_2211_ = v_a_2040_;
v___y_2212_ = v_a_2041_;
goto v___jp_2207_;
}
else
{
lean_object* v_inheritedTraceOptions_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v_inheritedTraceOptions_2255_ = lean_ctor_get(v_a_2040_, 13);
v___x_2256_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2255_, v_options_2252_, v___x_2256_);
if (v___x_2257_ == 0)
{
uint8_t v___x_2258_; 
lean_del_object(v___x_2242_);
lean_dec(v_candidate_2034_);
v___x_2258_ = lean_unbox(v_a_2250_);
lean_dec(v_a_2250_);
v___y_2208_ = v___x_2258_;
v___y_2209_ = v_a_2038_;
v___y_2210_ = v_a_2039_;
v___y_2211_ = v_a_2040_;
v___y_2212_ = v_a_2041_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2259_ = l_Lean_MessageData_ofName(v_candidate_2034_);
v___x_2260_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 7);
lean_ctor_set(v___x_2242_, 1, v___x_2260_);
lean_ctor_set(v___x_2242_, 0, v___x_2259_);
v___x_2262_ = v___x_2242_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2247_, v___x_2262_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2263_) == 0)
{
uint8_t v___x_2264_; 
lean_dec_ref(v___x_2263_);
v___x_2264_ = lean_unbox(v_a_2250_);
lean_dec(v_a_2250_);
v___y_2208_ = v___x_2264_;
v___y_2209_ = v_a_2038_;
v___y_2210_ = v_a_2039_;
v___y_2211_ = v_a_2040_;
v___y_2212_ = v_a_2041_;
goto v___jp_2207_;
}
else
{
lean_object* v_a_2265_; 
lean_dec(v_a_2250_);
lean_dec(v_constraints_2206_);
lean_dec(v_fst_2169_);
lean_dec(v_fst_2168_);
lean_dec(v_a_2112_);
v_a_2265_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2265_);
lean_dec_ref(v___x_2263_);
v_a_2072_ = v_a_2265_;
goto v___jp_2071_;
}
}
}
}
}
}
else
{
lean_object* v_a_2267_; 
lean_del_object(v___x_2242_);
lean_dec(v_constraints_2206_);
lean_dec(v_fst_2169_);
lean_dec(v_fst_2168_);
lean_dec(v_a_2112_);
lean_dec(v_candidate_2034_);
v_a_2267_ = lean_ctor_get(v___y_2249_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___y_2249_);
v_a_2072_ = v_a_2267_;
goto v___jp_2071_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2277_; 
lean_dec(v_a_2112_);
lean_dec_ref(v_s_2036_);
lean_dec_ref(v_t_2035_);
lean_dec(v_candidate_2034_);
v_a_2277_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2165_);
v_a_2072_ = v_a_2277_;
goto v___jp_2071_;
}
}
else
{
lean_object* v_a_2278_; 
lean_dec(v_a_2112_);
lean_dec_ref(v_s_2036_);
lean_dec_ref(v_t_2035_);
lean_dec(v_candidate_2034_);
v_a_2278_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2278_);
lean_dec_ref(v___x_2162_);
v_a_2072_ = v_a_2278_;
goto v___jp_2071_;
}
}
else
{
lean_object* v_a_2279_; 
lean_dec(v_a_2156_);
lean_dec(v_a_2112_);
lean_dec_ref(v_s_2036_);
lean_dec_ref(v_t_2035_);
lean_dec(v_candidate_2034_);
v_a_2279_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2279_);
lean_dec_ref(v___x_2159_);
v_a_2072_ = v_a_2279_;
goto v___jp_2071_;
}
}
else
{
lean_object* v_a_2280_; 
lean_dec(v_a_2112_);
lean_dec_ref(v_s_2036_);
lean_dec_ref(v_t_2035_);
lean_dec(v_candidate_2034_);
v_a_2280_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2155_);
v_a_2072_ = v_a_2280_;
goto v___jp_2071_;
}
v___jp_2113_:
{
if (v_a_2114_ == 0)
{
lean_dec(v_a_2112_);
v_a_2076_ = v_a_2114_;
goto v___jp_2075_;
}
else
{
uint8_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = 0;
v___x_2116_ = l_Lean_Meta_processPostponed(v_mayPostpone_2037_, v___x_2115_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2153_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2153_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2153_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
uint8_t v___x_2121_; 
v___x_2121_ = lean_unbox(v_a_2117_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; 
lean_del_object(v___x_2119_);
lean_dec(v_a_2117_);
lean_dec(v_a_2112_);
v___x_2122_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2044_, v_a_2039_, v_a_2041_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
lean_del_object(v___x_2046_);
lean_dec(v_a_2044_);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v___x_2122_, 0);
lean_dec(v_unused_2131_);
v___x_2124_ = v___x_2122_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v___x_2122_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_box(v___x_2115_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
lean_object* v_a_2132_; 
v_a_2132_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2122_);
v_a_2072_ = v_a_2132_;
goto v___jp_2071_;
}
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v_postponed_2135_; lean_object* v_mctx_2136_; lean_object* v_cache_2137_; lean_object* v_zetaDeltaFVarIds_2138_; lean_object* v_diag_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2151_; 
lean_del_object(v___x_2046_);
lean_dec(v_a_2044_);
v___x_2133_ = lean_st_ref_get(v_a_2039_);
v___x_2134_ = lean_st_ref_take(v_a_2039_);
v_postponed_2135_ = lean_ctor_get(v___x_2133_, 3);
lean_inc_ref(v_postponed_2135_);
lean_dec(v___x_2133_);
v_mctx_2136_ = lean_ctor_get(v___x_2134_, 0);
v_cache_2137_ = lean_ctor_get(v___x_2134_, 1);
v_zetaDeltaFVarIds_2138_ = lean_ctor_get(v___x_2134_, 2);
v_diag_2139_ = lean_ctor_get(v___x_2134_, 4);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v___x_2134_, 3);
lean_dec(v_unused_2152_);
v___x_2141_ = v___x_2134_;
v_isShared_2142_ = v_isSharedCheck_2151_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_diag_2139_);
lean_inc(v_zetaDeltaFVarIds_2138_);
lean_inc(v_cache_2137_);
lean_inc(v_mctx_2136_);
lean_dec(v___x_2134_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2151_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = l_Lean_PersistentArray_append___redArg(v_a_2112_, v_postponed_2135_);
lean_dec_ref(v_postponed_2135_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 3, v___x_2143_);
v___x_2145_ = v___x_2141_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_mctx_2136_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_cache_2137_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_zetaDeltaFVarIds_2138_);
lean_ctor_set(v_reuseFailAlloc_2150_, 3, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2150_, 4, v_diag_2139_);
v___x_2145_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_st_ref_set(v_a_2039_, v___x_2145_);
if (v_isShared_2120_ == 0)
{
v___x_2148_ = v___x_2119_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2117_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
}
else
{
lean_object* v_a_2154_; 
lean_dec(v_a_2112_);
v_a_2154_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2116_);
v_a_2072_ = v_a_2154_;
goto v___jp_2071_;
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_del_object(v___x_2046_);
lean_dec(v_a_2044_);
lean_dec_ref(v_s_2036_);
lean_dec_ref(v_t_2035_);
lean_dec(v_candidate_2034_);
v_a_2281_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2111_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2111_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
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
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v_s_2036_);
lean_dec_ref(v_t_2035_);
lean_dec(v_candidate_2034_);
v_a_2295_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2043_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2043_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object* v_candidate_2303_, lean_object* v_t_2304_, lean_object* v_s_2305_, lean_object* v_mayPostpone_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
uint8_t v_mayPostpone_boxed_2312_; lean_object* v_res_2313_; 
v_mayPostpone_boxed_2312_ = lean_unbox(v_mayPostpone_2306_);
v_res_2313_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2303_, v_t_2304_, v_s_2305_, v_mayPostpone_boxed_2312_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
return v_res_2313_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_unsigned_to_nat(32u);
v___x_2315_ = lean_mk_empty_array_with_capacity(v___x_2314_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2317_ = ((size_t)5ULL);
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = lean_unsigned_to_nat(32u);
v___x_2320_ = lean_mk_empty_array_with_capacity(v___x_2319_);
v___x_2321_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0);
v___x_2322_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v___x_2320_);
lean_ctor_set(v___x_2322_, 2, v___x_2318_);
lean_ctor_set(v___x_2322_, 3, v___x_2318_);
lean_ctor_set_usize(v___x_2322_, 4, v___x_2317_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v_traceState_2326_; lean_object* v_traces_2327_; lean_object* v___x_2328_; lean_object* v_traceState_2329_; lean_object* v_env_2330_; lean_object* v_nextMacroScope_2331_; lean_object* v_ngen_2332_; lean_object* v_auxDeclNGen_2333_; lean_object* v_cache_2334_; lean_object* v_messages_2335_; lean_object* v_infoState_2336_; lean_object* v_snapshotTasks_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2356_; 
v___x_2325_ = lean_st_ref_get(v___y_2323_);
v_traceState_2326_ = lean_ctor_get(v___x_2325_, 4);
lean_inc_ref(v_traceState_2326_);
lean_dec(v___x_2325_);
v_traces_2327_ = lean_ctor_get(v_traceState_2326_, 0);
lean_inc_ref(v_traces_2327_);
lean_dec_ref(v_traceState_2326_);
v___x_2328_ = lean_st_ref_take(v___y_2323_);
v_traceState_2329_ = lean_ctor_get(v___x_2328_, 4);
v_env_2330_ = lean_ctor_get(v___x_2328_, 0);
v_nextMacroScope_2331_ = lean_ctor_get(v___x_2328_, 1);
v_ngen_2332_ = lean_ctor_get(v___x_2328_, 2);
v_auxDeclNGen_2333_ = lean_ctor_get(v___x_2328_, 3);
v_cache_2334_ = lean_ctor_get(v___x_2328_, 5);
v_messages_2335_ = lean_ctor_get(v___x_2328_, 6);
v_infoState_2336_ = lean_ctor_get(v___x_2328_, 7);
v_snapshotTasks_2337_ = lean_ctor_get(v___x_2328_, 8);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2339_ = v___x_2328_;
v_isShared_2340_ = v_isSharedCheck_2356_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_snapshotTasks_2337_);
lean_inc(v_infoState_2336_);
lean_inc(v_messages_2335_);
lean_inc(v_cache_2334_);
lean_inc(v_traceState_2329_);
lean_inc(v_auxDeclNGen_2333_);
lean_inc(v_ngen_2332_);
lean_inc(v_nextMacroScope_2331_);
lean_inc(v_env_2330_);
lean_dec(v___x_2328_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2356_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
uint64_t v_tid_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2354_; 
v_tid_2341_ = lean_ctor_get_uint64(v_traceState_2329_, sizeof(void*)*1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_traceState_2329_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; 
v_unused_2355_ = lean_ctor_get(v_traceState_2329_, 0);
lean_dec(v_unused_2355_);
v___x_2343_ = v_traceState_2329_;
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
else
{
lean_dec(v_traceState_2329_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2345_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2345_);
v___x_2347_ = v___x_2343_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2345_);
lean_ctor_set_uint64(v_reuseFailAlloc_2353_, sizeof(void*)*1, v_tid_2341_);
v___x_2347_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 4, v___x_2347_);
v___x_2349_ = v___x_2339_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_env_2330_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_nextMacroScope_2331_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_ngen_2332_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_auxDeclNGen_2333_);
lean_ctor_set(v_reuseFailAlloc_2352_, 4, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2352_, 5, v_cache_2334_);
lean_ctor_set(v_reuseFailAlloc_2352_, 6, v_messages_2335_);
lean_ctor_set(v_reuseFailAlloc_2352_, 7, v_infoState_2336_);
lean_ctor_set(v_reuseFailAlloc_2352_, 8, v_snapshotTasks_2337_);
v___x_2349_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_st_ref_set(v___y_2323_, v___x_2349_);
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v_traces_2327_);
return v___x_2351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___boxed(lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2357_);
lean_dec(v___y_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
return v_res_2371_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object* v_opts_2372_, lean_object* v_opt_2373_){
_start:
{
lean_object* v_name_2374_; lean_object* v_defValue_2375_; lean_object* v_map_2376_; lean_object* v___x_2377_; 
v_name_2374_ = lean_ctor_get(v_opt_2373_, 0);
v_defValue_2375_ = lean_ctor_get(v_opt_2373_, 1);
v_map_2376_ = lean_ctor_get(v_opts_2372_, 0);
v___x_2377_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2376_, v_name_2374_);
if (lean_obj_tag(v___x_2377_) == 0)
{
uint8_t v___x_2378_; 
v___x_2378_ = lean_unbox(v_defValue_2375_);
return v___x_2378_;
}
else
{
lean_object* v_val_2379_; 
v_val_2379_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_val_2379_);
lean_dec_ref(v___x_2377_);
if (lean_obj_tag(v_val_2379_) == 1)
{
uint8_t v_v_2380_; 
v_v_2380_ = lean_ctor_get_uint8(v_val_2379_, 0);
lean_dec_ref(v_val_2379_);
return v_v_2380_;
}
else
{
uint8_t v___x_2381_; 
lean_dec(v_val_2379_);
v___x_2381_ = lean_unbox(v_defValue_2375_);
return v___x_2381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object* v_opts_2382_, lean_object* v_opt_2383_){
_start:
{
uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_res_2384_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2382_, v_opt_2383_);
lean_dec_ref(v_opt_2383_);
lean_dec_ref(v_opts_2382_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object* v_candidate_2395_, lean_object* v_t_2396_, lean_object* v_s_2397_, lean_object* v_x_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2404_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1);
v___x_2405_ = l_Lean_MessageData_ofName(v_candidate_2395_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3);
v___x_2408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = l_Lean_MessageData_ofExpr(v_t_2396_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l_Lean_MessageData_ofExpr(v_s_2397_);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object* v_candidate_2416_, lean_object* v_t_2417_, lean_object* v_s_2418_, lean_object* v_x_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(v_candidate_2416_, v_t_2417_, v_s_2418_, v_x_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec_ref(v_x_2419_);
return v_res_2425_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(lean_object* v_e_2426_){
_start:
{
if (lean_obj_tag(v_e_2426_) == 0)
{
uint8_t v___x_2427_; 
v___x_2427_ = 2;
return v___x_2427_;
}
else
{
lean_object* v_a_2428_; uint8_t v___x_2429_; 
v_a_2428_ = lean_ctor_get(v_e_2426_, 0);
v___x_2429_ = lean_unbox(v_a_2428_);
if (v___x_2429_ == 0)
{
uint8_t v___x_2430_; 
v___x_2430_ = 1;
return v___x_2430_;
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = 0;
return v___x_2431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(lean_object* v_e_2432_){
_start:
{
uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_res_2433_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_e_2432_);
lean_dec_ref(v_e_2432_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(lean_object* v_opts_2435_, lean_object* v_opt_2436_){
_start:
{
lean_object* v_name_2437_; lean_object* v_defValue_2438_; lean_object* v_map_2439_; lean_object* v___x_2440_; 
v_name_2437_ = lean_ctor_get(v_opt_2436_, 0);
v_defValue_2438_ = lean_ctor_get(v_opt_2436_, 1);
v_map_2439_ = lean_ctor_get(v_opts_2435_, 0);
v___x_2440_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2439_, v_name_2437_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_inc(v_defValue_2438_);
return v_defValue_2438_;
}
else
{
lean_object* v_val_2441_; 
v_val_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_val_2441_);
lean_dec_ref(v___x_2440_);
if (lean_obj_tag(v_val_2441_) == 3)
{
lean_object* v_v_2442_; 
v_v_2442_ = lean_ctor_get(v_val_2441_, 0);
lean_inc(v_v_2442_);
lean_dec_ref(v_val_2441_);
return v_v_2442_;
}
else
{
lean_dec(v_val_2441_);
lean_inc(v_defValue_2438_);
return v_defValue_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(lean_object* v_opts_2443_, lean_object* v_opt_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2443_, v_opt_2444_);
lean_dec_ref(v_opt_2444_);
lean_dec_ref(v_opts_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(lean_object* v_x_2446_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_a_2448_ = lean_ctor_get(v_x_2446_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_x_2446_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v_x_2446_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v_x_2446_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set_tag(v___x_2450_, 1);
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
v_a_2456_ = lean_ctor_get(v_x_2446_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_x_2446_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v_x_2446_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v_x_2446_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set_tag(v___x_2458_, 0);
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg___boxed(lean_object* v_x_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_x_2464_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(size_t v_sz_2467_, size_t v_i_2468_, lean_object* v_bs_2469_){
_start:
{
uint8_t v___x_2470_; 
v___x_2470_ = lean_usize_dec_lt(v_i_2468_, v_sz_2467_);
if (v___x_2470_ == 0)
{
return v_bs_2469_;
}
else
{
lean_object* v_v_2471_; lean_object* v_msg_2472_; lean_object* v___x_2473_; lean_object* v_bs_x27_2474_; size_t v___x_2475_; size_t v___x_2476_; lean_object* v___x_2477_; 
v_v_2471_ = lean_array_uget_borrowed(v_bs_2469_, v_i_2468_);
v_msg_2472_ = lean_ctor_get(v_v_2471_, 1);
lean_inc_ref(v_msg_2472_);
v___x_2473_ = lean_unsigned_to_nat(0u);
v_bs_x27_2474_ = lean_array_uset(v_bs_2469_, v_i_2468_, v___x_2473_);
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2468_, v___x_2475_);
v___x_2477_ = lean_array_uset(v_bs_x27_2474_, v_i_2468_, v_msg_2472_);
v_i_2468_ = v___x_2476_;
v_bs_2469_ = v___x_2477_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9___boxed(lean_object* v_sz_2479_, lean_object* v_i_2480_, lean_object* v_bs_2481_){
_start:
{
size_t v_sz_boxed_2482_; size_t v_i_boxed_2483_; lean_object* v_res_2484_; 
v_sz_boxed_2482_ = lean_unbox_usize(v_sz_2479_);
lean_dec(v_sz_2479_);
v_i_boxed_2483_ = lean_unbox_usize(v_i_2480_);
lean_dec(v_i_2480_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(v_sz_boxed_2482_, v_i_boxed_2483_, v_bs_2481_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(lean_object* v_oldTraces_2485_, lean_object* v_data_2486_, lean_object* v_ref_2487_, lean_object* v_msg_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_fileName_2494_; lean_object* v_fileMap_2495_; lean_object* v_options_2496_; lean_object* v_currRecDepth_2497_; lean_object* v_maxRecDepth_2498_; lean_object* v_ref_2499_; lean_object* v_currNamespace_2500_; lean_object* v_openDecls_2501_; lean_object* v_initHeartbeats_2502_; lean_object* v_maxHeartbeats_2503_; lean_object* v_quotContext_2504_; lean_object* v_currMacroScope_2505_; uint8_t v_diag_2506_; lean_object* v_cancelTk_x3f_2507_; uint8_t v_suppressElabErrors_2508_; lean_object* v_inheritedTraceOptions_2509_; lean_object* v___x_2510_; lean_object* v_traceState_2511_; lean_object* v_traces_2512_; lean_object* v_ref_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; size_t v_sz_2516_; size_t v___x_2517_; lean_object* v___x_2518_; lean_object* v_msg_2519_; lean_object* v___x_2520_; lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2558_; 
v_fileName_2494_ = lean_ctor_get(v___y_2491_, 0);
v_fileMap_2495_ = lean_ctor_get(v___y_2491_, 1);
v_options_2496_ = lean_ctor_get(v___y_2491_, 2);
v_currRecDepth_2497_ = lean_ctor_get(v___y_2491_, 3);
v_maxRecDepth_2498_ = lean_ctor_get(v___y_2491_, 4);
v_ref_2499_ = lean_ctor_get(v___y_2491_, 5);
v_currNamespace_2500_ = lean_ctor_get(v___y_2491_, 6);
v_openDecls_2501_ = lean_ctor_get(v___y_2491_, 7);
v_initHeartbeats_2502_ = lean_ctor_get(v___y_2491_, 8);
v_maxHeartbeats_2503_ = lean_ctor_get(v___y_2491_, 9);
v_quotContext_2504_ = lean_ctor_get(v___y_2491_, 10);
v_currMacroScope_2505_ = lean_ctor_get(v___y_2491_, 11);
v_diag_2506_ = lean_ctor_get_uint8(v___y_2491_, sizeof(void*)*14);
v_cancelTk_x3f_2507_ = lean_ctor_get(v___y_2491_, 12);
v_suppressElabErrors_2508_ = lean_ctor_get_uint8(v___y_2491_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2509_ = lean_ctor_get(v___y_2491_, 13);
v___x_2510_ = lean_st_ref_get(v___y_2492_);
v_traceState_2511_ = lean_ctor_get(v___x_2510_, 4);
lean_inc_ref(v_traceState_2511_);
lean_dec(v___x_2510_);
v_traces_2512_ = lean_ctor_get(v_traceState_2511_, 0);
lean_inc_ref(v_traces_2512_);
lean_dec_ref(v_traceState_2511_);
v_ref_2513_ = l_Lean_replaceRef(v_ref_2487_, v_ref_2499_);
lean_inc_ref(v_inheritedTraceOptions_2509_);
lean_inc(v_cancelTk_x3f_2507_);
lean_inc(v_currMacroScope_2505_);
lean_inc(v_quotContext_2504_);
lean_inc(v_maxHeartbeats_2503_);
lean_inc(v_initHeartbeats_2502_);
lean_inc(v_openDecls_2501_);
lean_inc(v_currNamespace_2500_);
lean_inc(v_maxRecDepth_2498_);
lean_inc(v_currRecDepth_2497_);
lean_inc_ref(v_options_2496_);
lean_inc_ref(v_fileMap_2495_);
lean_inc_ref(v_fileName_2494_);
v___x_2514_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2514_, 0, v_fileName_2494_);
lean_ctor_set(v___x_2514_, 1, v_fileMap_2495_);
lean_ctor_set(v___x_2514_, 2, v_options_2496_);
lean_ctor_set(v___x_2514_, 3, v_currRecDepth_2497_);
lean_ctor_set(v___x_2514_, 4, v_maxRecDepth_2498_);
lean_ctor_set(v___x_2514_, 5, v_ref_2513_);
lean_ctor_set(v___x_2514_, 6, v_currNamespace_2500_);
lean_ctor_set(v___x_2514_, 7, v_openDecls_2501_);
lean_ctor_set(v___x_2514_, 8, v_initHeartbeats_2502_);
lean_ctor_set(v___x_2514_, 9, v_maxHeartbeats_2503_);
lean_ctor_set(v___x_2514_, 10, v_quotContext_2504_);
lean_ctor_set(v___x_2514_, 11, v_currMacroScope_2505_);
lean_ctor_set(v___x_2514_, 12, v_cancelTk_x3f_2507_);
lean_ctor_set(v___x_2514_, 13, v_inheritedTraceOptions_2509_);
lean_ctor_set_uint8(v___x_2514_, sizeof(void*)*14, v_diag_2506_);
lean_ctor_set_uint8(v___x_2514_, sizeof(void*)*14 + 1, v_suppressElabErrors_2508_);
v___x_2515_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2512_);
lean_dec_ref(v_traces_2512_);
v_sz_2516_ = lean_array_size(v___x_2515_);
v___x_2517_ = ((size_t)0ULL);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(v_sz_2516_, v___x_2517_, v___x_2515_);
v_msg_2519_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2519_, 0, v_data_2486_);
lean_ctor_set(v_msg_2519_, 1, v_msg_2488_);
lean_ctor_set(v_msg_2519_, 2, v___x_2518_);
v___x_2520_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2519_, v___y_2489_, v___y_2490_, v___x_2514_, v___y_2492_);
lean_dec_ref(v___x_2514_);
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2558_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2558_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v_traceState_2526_; lean_object* v_env_2527_; lean_object* v_nextMacroScope_2528_; lean_object* v_ngen_2529_; lean_object* v_auxDeclNGen_2530_; lean_object* v_cache_2531_; lean_object* v_messages_2532_; lean_object* v_infoState_2533_; lean_object* v_snapshotTasks_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2557_; 
v___x_2525_ = lean_st_ref_take(v___y_2492_);
v_traceState_2526_ = lean_ctor_get(v___x_2525_, 4);
v_env_2527_ = lean_ctor_get(v___x_2525_, 0);
v_nextMacroScope_2528_ = lean_ctor_get(v___x_2525_, 1);
v_ngen_2529_ = lean_ctor_get(v___x_2525_, 2);
v_auxDeclNGen_2530_ = lean_ctor_get(v___x_2525_, 3);
v_cache_2531_ = lean_ctor_get(v___x_2525_, 5);
v_messages_2532_ = lean_ctor_get(v___x_2525_, 6);
v_infoState_2533_ = lean_ctor_get(v___x_2525_, 7);
v_snapshotTasks_2534_ = lean_ctor_get(v___x_2525_, 8);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2536_ = v___x_2525_;
v_isShared_2537_ = v_isSharedCheck_2557_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_snapshotTasks_2534_);
lean_inc(v_infoState_2533_);
lean_inc(v_messages_2532_);
lean_inc(v_cache_2531_);
lean_inc(v_traceState_2526_);
lean_inc(v_auxDeclNGen_2530_);
lean_inc(v_ngen_2529_);
lean_inc(v_nextMacroScope_2528_);
lean_inc(v_env_2527_);
lean_dec(v___x_2525_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2557_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
uint64_t v_tid_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2555_; 
v_tid_2538_ = lean_ctor_get_uint64(v_traceState_2526_, sizeof(void*)*1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_traceState_2526_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v_traceState_2526_, 0);
lean_dec(v_unused_2556_);
v___x_2540_ = v_traceState_2526_;
v_isShared_2541_ = v_isSharedCheck_2555_;
goto v_resetjp_2539_;
}
else
{
lean_dec(v_traceState_2526_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2555_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_ref_2487_);
lean_ctor_set(v___x_2542_, 1, v_a_2521_);
v___x_2543_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2485_, v___x_2542_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2543_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2543_);
lean_ctor_set_uint64(v_reuseFailAlloc_2554_, sizeof(void*)*1, v_tid_2538_);
v___x_2545_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 4, v___x_2545_);
v___x_2547_ = v___x_2536_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_env_2527_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_nextMacroScope_2528_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_ngen_2529_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_auxDeclNGen_2530_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2553_, 5, v_cache_2531_);
lean_ctor_set(v_reuseFailAlloc_2553_, 6, v_messages_2532_);
lean_ctor_set(v_reuseFailAlloc_2553_, 7, v_infoState_2533_);
lean_ctor_set(v_reuseFailAlloc_2553_, 8, v_snapshotTasks_2534_);
v___x_2547_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2548_ = lean_st_ref_set(v___y_2492_, v___x_2547_);
v___x_2549_ = lean_box(0);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2549_);
v___x_2551_ = v___x_2523_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(lean_object* v_oldTraces_2559_, lean_object* v_data_2560_, lean_object* v_ref_2561_, lean_object* v_msg_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_oldTraces_2559_, v_data_2560_, v_ref_2561_, v_msg_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2568_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0));
v___x_2571_ = l_Lean_stringToMessageData(v___x_2570_);
return v___x_2571_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2));
v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
return v___x_2574_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4(void){
_start:
{
lean_object* v___x_2575_; double v___x_2576_; 
v___x_2575_ = lean_unsigned_to_nat(1000u);
v___x_2576_ = lean_float_of_nat(v___x_2575_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object* v_cls_2577_, uint8_t v_collapsed_2578_, lean_object* v_tag_2579_, lean_object* v_opts_2580_, uint8_t v_clsEnabled_2581_, lean_object* v_oldTraces_2582_, lean_object* v_msg_2583_, lean_object* v_resStartStop_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_fst_2590_; lean_object* v_snd_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2689_; 
v_fst_2590_ = lean_ctor_get(v_resStartStop_2584_, 0);
v_snd_2591_ = lean_ctor_get(v_resStartStop_2584_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_resStartStop_2584_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2593_ = v_resStartStop_2584_;
v_isShared_2594_ = v_isSharedCheck_2689_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_snd_2591_);
lean_inc(v_fst_2590_);
lean_dec(v_resStartStop_2584_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2689_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v_data_2598_; lean_object* v_fst_2609_; lean_object* v_snd_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2688_; 
v_fst_2609_ = lean_ctor_get(v_snd_2591_, 0);
v_snd_2610_ = lean_ctor_get(v_snd_2591_, 1);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_snd_2591_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2612_ = v_snd_2591_;
v_isShared_2613_ = v_isSharedCheck_2688_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_snd_2610_);
lean_inc(v_fst_2609_);
lean_dec(v_snd_2591_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2688_;
goto v_resetjp_2611_;
}
v___jp_2595_:
{
lean_object* v___x_2599_; 
lean_inc(v___y_2596_);
v___x_2599_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_oldTraces_2582_, v_data_2598_, v___y_2596_, v___y_2597_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v___x_2600_; 
lean_dec_ref(v___x_2599_);
v___x_2600_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_fst_2590_);
return v___x_2600_;
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec(v_fst_2590_);
v_a_2601_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2599_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2599_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; uint8_t v___x_2615_; lean_object* v___y_2617_; lean_object* v_a_2618_; uint8_t v___y_2642_; double v___y_2673_; 
v___x_2614_ = l_Lean_trace_profiler;
v___x_2615_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2580_, v___x_2614_);
if (v___x_2615_ == 0)
{
v___y_2642_ = v___x_2615_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2678_; uint8_t v___x_2679_; 
v___x_2678_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2679_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2580_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; double v___x_2682_; double v___x_2683_; double v___x_2684_; 
v___x_2680_ = l_Lean_trace_profiler_threshold;
v___x_2681_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2580_, v___x_2680_);
v___x_2682_ = lean_float_of_nat(v___x_2681_);
v___x_2683_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4);
v___x_2684_ = lean_float_div(v___x_2682_, v___x_2683_);
v___y_2673_ = v___x_2684_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; double v___x_2687_; 
v___x_2685_ = l_Lean_trace_profiler_threshold;
v___x_2686_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2580_, v___x_2685_);
v___x_2687_ = lean_float_of_nat(v___x_2686_);
v___y_2673_ = v___x_2687_;
goto v___jp_2672_;
}
}
v___jp_2616_:
{
uint8_t v_result_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v_result_2619_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_fst_2590_);
v___x_2620_ = l_Lean_TraceResult_toEmoji(v_result_2619_);
v___x_2621_ = l_Lean_stringToMessageData(v___x_2620_);
v___x_2622_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 7);
lean_ctor_set(v___x_2612_, 1, v___x_2622_);
lean_ctor_set(v___x_2612_, 0, v___x_2621_);
v___x_2624_ = v___x_2612_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v_m_2626_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 7);
lean_ctor_set(v___x_2593_, 1, v_a_2618_);
lean_ctor_set(v___x_2593_, 0, v___x_2624_);
v_m_2626_ = v___x_2593_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_a_2618_);
v_m_2626_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; double v___x_2629_; lean_object* v_data_2630_; 
v___x_2627_ = lean_box(v_result_2619_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
v___x_2629_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
lean_inc_ref(v_tag_2579_);
lean_inc_ref(v___x_2628_);
lean_inc(v_cls_2577_);
v_data_2630_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2630_, 0, v_cls_2577_);
lean_ctor_set(v_data_2630_, 1, v___x_2628_);
lean_ctor_set(v_data_2630_, 2, v_tag_2579_);
lean_ctor_set_float(v_data_2630_, sizeof(void*)*3, v___x_2629_);
lean_ctor_set_float(v_data_2630_, sizeof(void*)*3 + 8, v___x_2629_);
lean_ctor_set_uint8(v_data_2630_, sizeof(void*)*3 + 16, v_collapsed_2578_);
if (v___x_2615_ == 0)
{
lean_dec_ref(v___x_2628_);
lean_dec(v_snd_2610_);
lean_dec(v_fst_2609_);
lean_dec_ref(v_tag_2579_);
lean_dec(v_cls_2577_);
v___y_2596_ = v___y_2617_;
v___y_2597_ = v_m_2626_;
v_data_2598_ = v_data_2630_;
goto v___jp_2595_;
}
else
{
lean_object* v_data_2631_; double v___x_2632_; double v___x_2633_; 
lean_dec_ref(v_data_2630_);
v_data_2631_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2631_, 0, v_cls_2577_);
lean_ctor_set(v_data_2631_, 1, v___x_2628_);
lean_ctor_set(v_data_2631_, 2, v_tag_2579_);
v___x_2632_ = lean_unbox_float(v_fst_2609_);
lean_dec(v_fst_2609_);
lean_ctor_set_float(v_data_2631_, sizeof(void*)*3, v___x_2632_);
v___x_2633_ = lean_unbox_float(v_snd_2610_);
lean_dec(v_snd_2610_);
lean_ctor_set_float(v_data_2631_, sizeof(void*)*3 + 8, v___x_2633_);
lean_ctor_set_uint8(v_data_2631_, sizeof(void*)*3 + 16, v_collapsed_2578_);
v___y_2596_ = v___y_2617_;
v___y_2597_ = v_m_2626_;
v_data_2598_ = v_data_2631_;
goto v___jp_2595_;
}
}
}
}
v___jp_2636_:
{
lean_object* v_ref_2637_; lean_object* v___x_2638_; 
v_ref_2637_ = lean_ctor_get(v___y_2587_, 5);
lean_inc(v___y_2588_);
lean_inc_ref(v___y_2587_);
lean_inc(v___y_2586_);
lean_inc_ref(v___y_2585_);
lean_inc(v_fst_2590_);
v___x_2638_ = lean_apply_6(v_msg_2583_, v_fst_2590_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, lean_box(0));
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref(v___x_2638_);
v___y_2617_ = v_ref_2637_;
v_a_2618_ = v_a_2639_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2640_; 
lean_dec_ref(v___x_2638_);
v___x_2640_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3);
v___y_2617_ = v_ref_2637_;
v_a_2618_ = v___x_2640_;
goto v___jp_2616_;
}
}
v___jp_2641_:
{
if (v_clsEnabled_2581_ == 0)
{
if (v___y_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v_traceState_2644_; lean_object* v_env_2645_; lean_object* v_nextMacroScope_2646_; lean_object* v_ngen_2647_; lean_object* v_auxDeclNGen_2648_; lean_object* v_cache_2649_; lean_object* v_messages_2650_; lean_object* v_infoState_2651_; lean_object* v_snapshotTasks_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2671_; 
lean_del_object(v___x_2612_);
lean_dec(v_snd_2610_);
lean_dec(v_fst_2609_);
lean_del_object(v___x_2593_);
lean_dec_ref(v_msg_2583_);
lean_dec_ref(v_tag_2579_);
lean_dec(v_cls_2577_);
v___x_2643_ = lean_st_ref_take(v___y_2588_);
v_traceState_2644_ = lean_ctor_get(v___x_2643_, 4);
v_env_2645_ = lean_ctor_get(v___x_2643_, 0);
v_nextMacroScope_2646_ = lean_ctor_get(v___x_2643_, 1);
v_ngen_2647_ = lean_ctor_get(v___x_2643_, 2);
v_auxDeclNGen_2648_ = lean_ctor_get(v___x_2643_, 3);
v_cache_2649_ = lean_ctor_get(v___x_2643_, 5);
v_messages_2650_ = lean_ctor_get(v___x_2643_, 6);
v_infoState_2651_ = lean_ctor_get(v___x_2643_, 7);
v_snapshotTasks_2652_ = lean_ctor_get(v___x_2643_, 8);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2654_ = v___x_2643_;
v_isShared_2655_ = v_isSharedCheck_2671_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_snapshotTasks_2652_);
lean_inc(v_infoState_2651_);
lean_inc(v_messages_2650_);
lean_inc(v_cache_2649_);
lean_inc(v_traceState_2644_);
lean_inc(v_auxDeclNGen_2648_);
lean_inc(v_ngen_2647_);
lean_inc(v_nextMacroScope_2646_);
lean_inc(v_env_2645_);
lean_dec(v___x_2643_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2671_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
uint64_t v_tid_2656_; lean_object* v_traces_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2670_; 
v_tid_2656_ = lean_ctor_get_uint64(v_traceState_2644_, sizeof(void*)*1);
v_traces_2657_ = lean_ctor_get(v_traceState_2644_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_traceState_2644_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2659_ = v_traceState_2644_;
v_isShared_2660_ = v_isSharedCheck_2670_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_traces_2657_);
lean_dec(v_traceState_2644_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2670_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2661_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2582_, v_traces_2657_);
lean_dec_ref(v_traces_2657_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2661_);
v___x_2663_ = v___x_2659_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2661_);
lean_ctor_set_uint64(v_reuseFailAlloc_2669_, sizeof(void*)*1, v_tid_2656_);
v___x_2663_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2665_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 4, v___x_2663_);
v___x_2665_ = v___x_2654_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_env_2645_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_nextMacroScope_2646_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v_ngen_2647_);
lean_ctor_set(v_reuseFailAlloc_2668_, 3, v_auxDeclNGen_2648_);
lean_ctor_set(v_reuseFailAlloc_2668_, 4, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2668_, 5, v_cache_2649_);
lean_ctor_set(v_reuseFailAlloc_2668_, 6, v_messages_2650_);
lean_ctor_set(v_reuseFailAlloc_2668_, 7, v_infoState_2651_);
lean_ctor_set(v_reuseFailAlloc_2668_, 8, v_snapshotTasks_2652_);
v___x_2665_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = lean_st_ref_set(v___y_2588_, v___x_2665_);
v___x_2667_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_fst_2590_);
return v___x_2667_;
}
}
}
}
}
else
{
goto v___jp_2636_;
}
}
else
{
goto v___jp_2636_;
}
}
v___jp_2672_:
{
double v___x_2674_; double v___x_2675_; double v___x_2676_; uint8_t v___x_2677_; 
v___x_2674_ = lean_unbox_float(v_snd_2610_);
v___x_2675_ = lean_unbox_float(v_fst_2609_);
v___x_2676_ = lean_float_sub(v___x_2674_, v___x_2675_);
v___x_2677_ = lean_float_decLt(v___y_2673_, v___x_2676_);
v___y_2642_ = v___x_2677_;
goto v___jp_2641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object* v_cls_2690_, lean_object* v_collapsed_2691_, lean_object* v_tag_2692_, lean_object* v_opts_2693_, lean_object* v_clsEnabled_2694_, lean_object* v_oldTraces_2695_, lean_object* v_msg_2696_, lean_object* v_resStartStop_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
uint8_t v_collapsed_boxed_2703_; uint8_t v_clsEnabled_boxed_2704_; lean_object* v_res_2705_; 
v_collapsed_boxed_2703_ = lean_unbox(v_collapsed_2691_);
v_clsEnabled_boxed_2704_ = lean_unbox(v_clsEnabled_2694_);
v_res_2705_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2690_, v_collapsed_boxed_2703_, v_tag_2692_, v_opts_2693_, v_clsEnabled_boxed_2704_, v_oldTraces_2695_, v_msg_2696_, v_resStartStop_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_opts_2693_);
return v_res_2705_;
}
}
static double _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0(void){
_start:
{
lean_object* v___x_2706_; double v___x_2707_; 
v___x_2706_ = lean_unsigned_to_nat(1000000000u);
v___x_2707_ = lean_float_of_nat(v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object* v_t_2708_, lean_object* v_s_2709_, lean_object* v_candidate_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_options_2716_; lean_object* v_inheritedTraceOptions_2717_; uint8_t v_hasTrace_2718_; uint8_t v___x_2719_; 
v_options_2716_ = lean_ctor_get(v_a_2713_, 2);
v_inheritedTraceOptions_2717_ = lean_ctor_get(v_a_2713_, 13);
v_hasTrace_2718_ = lean_ctor_get_uint8(v_options_2716_, sizeof(void*)*1);
v___x_2719_ = 1;
if (v_hasTrace_2718_ == 0)
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2710_, v_t_2708_, v_s_2709_, v___x_2719_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2720_;
}
else
{
lean_object* v___f_2721_; lean_object* v_cls_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v_a_2729_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v_a_2744_; 
lean_inc_ref(v_s_2709_);
lean_inc_ref(v_t_2708_);
lean_inc(v_candidate_2710_);
v___f_2721_ = lean_alloc_closure((void*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2721_, 0, v_candidate_2710_);
lean_closure_set(v___f_2721_, 1, v_t_2708_);
lean_closure_set(v___f_2721_, 2, v_s_2709_);
v_cls_2722_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2723_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_2724_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2725_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2717_, v_options_2716_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2794_ = l_Lean_trace_profiler;
v___x_2795_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2716_, v___x_2794_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; 
lean_dec_ref(v___f_2721_);
v___x_2796_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2710_, v_t_2708_, v_s_2709_, v___x_2719_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2796_;
}
else
{
goto v___jp_2753_;
}
}
else
{
goto v___jp_2753_;
}
v___jp_2726_:
{
lean_object* v___x_2730_; double v___x_2731_; double v___x_2732_; double v___x_2733_; double v___x_2734_; double v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2730_ = lean_io_mono_nanos_now();
v___x_2731_ = lean_float_of_nat(v___y_2727_);
v___x_2732_ = lean_float_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0);
v___x_2733_ = lean_float_div(v___x_2731_, v___x_2732_);
v___x_2734_ = lean_float_of_nat(v___x_2730_);
v___x_2735_ = lean_float_div(v___x_2734_, v___x_2732_);
v___x_2736_ = lean_box_float(v___x_2733_);
v___x_2737_ = lean_box_float(v___x_2735_);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2739_, 0, v_a_2729_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2722_, v___x_2719_, v___x_2723_, v_options_2716_, v___x_2725_, v___y_2728_, v___f_2721_, v___x_2739_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2740_;
}
v___jp_2741_:
{
lean_object* v___x_2745_; double v___x_2746_; double v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2745_ = lean_io_get_num_heartbeats();
v___x_2746_ = lean_float_of_nat(v___y_2742_);
v___x_2747_ = lean_float_of_nat(v___x_2745_);
v___x_2748_ = lean_box_float(v___x_2746_);
v___x_2749_ = lean_box_float(v___x_2747_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v_a_2744_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2722_, v___x_2719_, v___x_2723_, v_options_2716_, v___x_2725_, v___y_2743_, v___f_2721_, v___x_2751_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2752_;
}
v___jp_2753_:
{
lean_object* v___x_2754_; lean_object* v_a_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2754_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v_a_2714_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2754_);
v___x_2756_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2757_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2716_, v___x_2756_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_io_mono_nanos_now();
v___x_2759_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2710_, v_t_2708_, v_s_2709_, v___x_2719_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 1);
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
v___y_2727_ = v___x_2758_;
v___y_2728_ = v_a_2755_;
v_a_2729_ = v___x_2765_;
goto v___jp_2726_;
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_a_2768_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2759_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2759_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 0);
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
v___y_2727_ = v___x_2758_;
v___y_2728_ = v_a_2755_;
v_a_2729_ = v___x_2773_;
goto v___jp_2726_;
}
}
}
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_io_get_num_heartbeats();
v___x_2777_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2710_, v_t_2708_, v_s_2709_, v___x_2719_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 1);
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
v___y_2742_ = v___x_2776_;
v___y_2743_ = v_a_2755_;
v_a_2744_ = v___x_2783_;
goto v___jp_2741_;
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_a_2786_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2777_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2777_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set_tag(v___x_2788_, 0);
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
v___y_2742_ = v___x_2776_;
v___y_2743_ = v_a_2755_;
v_a_2744_ = v___x_2791_;
goto v___jp_2741_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object* v_t_2797_, lean_object* v_s_2798_, lean_object* v_candidate_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2797_, v_s_2798_, v_candidate_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object* v_as_2806_, lean_object* v_as_x27_2807_, lean_object* v_b_2808_, lean_object* v_a_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2807_, v_b_2808_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object* v_as_2816_, lean_object* v_as_x27_2817_, lean_object* v_b_2818_, lean_object* v_a_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(v_as_2816_, v_as_x27_2817_, v_b_2818_, v_a_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v_as_2816_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(lean_object* v_00_u03b1_2826_, lean_object* v_x_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_x_2827_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2834_, lean_object* v_x_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_00_u03b1_2834_, v_x_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(lean_object* v_t_2842_, lean_object* v_s_2843_, uint8_t v___x_2844_, lean_object* v_as_2845_, size_t v_sz_2846_, size_t v_i_2847_, lean_object* v_b_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_usize_dec_lt(v_i_2847_, v_sz_2846_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec_ref(v_s_2843_);
lean_dec_ref(v_t_2842_);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v_b_2848_);
return v___x_2855_;
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
lean_dec_ref(v_b_2848_);
v_a_2856_ = lean_array_uget_borrowed(v_as_2845_, v_i_2847_);
lean_inc(v_a_2856_);
lean_inc_ref(v_s_2843_);
lean_inc_ref(v_t_2842_);
v___x_2857_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2842_, v_s_2843_, v_a_2856_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2874_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2874_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2874_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2862_ = lean_box(0);
v___x_2863_ = lean_unbox(v_a_2858_);
lean_dec(v_a_2858_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; size_t v___x_2865_; size_t v___x_2866_; 
lean_del_object(v___x_2860_);
v___x_2864_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v___x_2865_ = ((size_t)1ULL);
v___x_2866_ = lean_usize_add(v_i_2847_, v___x_2865_);
v_i_2847_ = v___x_2866_;
v_b_2848_ = v___x_2864_;
goto _start;
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2872_; 
lean_dec_ref(v_s_2843_);
lean_dec_ref(v_t_2842_);
v___x_2868_ = lean_box(v___x_2844_);
v___x_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set(v___x_2870_, 1, v___x_2862_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2870_);
v___x_2872_ = v___x_2860_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec_ref(v_s_2843_);
lean_dec_ref(v_t_2842_);
v_a_2875_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2857_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2857_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object* v_t_2883_, lean_object* v_s_2884_, lean_object* v___x_2885_, lean_object* v_as_2886_, lean_object* v_sz_2887_, lean_object* v_i_2888_, lean_object* v_b_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
uint8_t v___x_3585__boxed_2895_; size_t v_sz_boxed_2896_; size_t v_i_boxed_2897_; lean_object* v_res_2898_; 
v___x_3585__boxed_2895_ = lean_unbox(v___x_2885_);
v_sz_boxed_2896_ = lean_unbox_usize(v_sz_2887_);
lean_dec(v_sz_2887_);
v_i_boxed_2897_ = lean_unbox_usize(v_i_2888_);
lean_dec(v_i_2888_);
v_res_2898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2883_, v_s_2884_, v___x_3585__boxed_2895_, v_as_2886_, v_sz_boxed_2896_, v_i_boxed_2897_, v_b_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v_as_2886_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* v_t_2899_, lean_object* v_s_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v_options_2978_; uint8_t v_hasTrace_2979_; 
v_options_2978_ = lean_ctor_get(v_a_2903_, 2);
v_hasTrace_2979_ = lean_ctor_get_uint8(v_options_2978_, sizeof(void*)*1);
if (v_hasTrace_2979_ == 0)
{
v___y_2907_ = v_a_2901_;
v___y_2908_ = v_a_2902_;
v___y_2909_ = v_a_2903_;
v___y_2910_ = v_a_2904_;
goto v___jp_2906_;
}
else
{
lean_object* v_inheritedTraceOptions_2980_; lean_object* v_cls_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v_inheritedTraceOptions_2980_ = lean_ctor_get(v_a_2903_, 13);
v_cls_2981_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2982_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2983_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2980_, v_options_2978_, v___x_2982_);
if (v___x_2983_ == 0)
{
v___y_2907_ = v_a_2901_;
v___y_2908_ = v_a_2902_;
v___y_2909_ = v_a_2903_;
v___y_2910_ = v_a_2904_;
goto v___jp_2906_;
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_inc_ref(v_t_2899_);
v___x_2984_ = l_Lean_MessageData_ofExpr(v_t_2899_);
v___x_2985_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
lean_inc_ref(v_s_2900_);
v___x_2987_ = l_Lean_MessageData_ofExpr(v_s_2900_);
v___x_2988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2981_, v___x_2988_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_dec_ref(v___x_2989_);
v___y_2907_ = v_a_2901_;
v___y_2908_ = v_a_2902_;
v___y_2909_ = v_a_2903_;
v___y_2910_ = v_a_2904_;
goto v___jp_2906_;
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref(v_s_2900_);
lean_dec_ref(v_t_2899_);
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
v___jp_2906_:
{
lean_object* v___x_2911_; uint8_t v_unificationHints_2912_; 
v___x_2911_ = l_Lean_Meta_Context_config(v___y_2907_);
v_unificationHints_2912_ = lean_ctor_get_uint8(v___x_2911_, 5);
lean_dec_ref(v___x_2911_);
if (v_unificationHints_2912_ == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
lean_dec_ref(v_s_2900_);
lean_dec_ref(v_t_2899_);
v___x_2913_ = lean_box(v_unificationHints_2912_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
else
{
uint8_t v___x_2915_; 
v___x_2915_ = l_Lean_Expr_isMVar(v_t_2899_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v_env_2917_; lean_object* v___x_2918_; lean_object* v_ext_2919_; lean_object* v_toEnvExtension_2920_; lean_object* v_asyncMode_2921_; lean_object* v___x_2922_; lean_object* v_config_2923_; uint8_t v_trackZetaDelta_2924_; lean_object* v_zetaDeltaSet_2925_; lean_object* v_lctx_2926_; lean_object* v_localInstances_2927_; lean_object* v_defEqCtx_x3f_2928_; lean_object* v_synthPendingDepth_2929_; lean_object* v_canUnfold_x3f_2930_; uint8_t v_univApprox_2931_; uint8_t v_inTypeClassResolution_2932_; uint8_t v_cacheInferType_2933_; uint64_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2916_ = lean_st_ref_get(v___y_2910_);
v_env_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc_ref(v_env_2917_);
lean_dec(v___x_2916_);
v___x_2918_ = l_Lean_Meta_unificationHintExtension;
v_ext_2919_ = lean_ctor_get(v___x_2918_, 1);
v_toEnvExtension_2920_ = lean_ctor_get(v_ext_2919_, 0);
v_asyncMode_2921_ = lean_ctor_get(v_toEnvExtension_2920_, 2);
v___x_2922_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_2923_ = lean_ctor_get(v___x_2922_, 0);
v_trackZetaDelta_2924_ = lean_ctor_get_uint8(v___y_2907_, sizeof(void*)*7);
v_zetaDeltaSet_2925_ = lean_ctor_get(v___y_2907_, 1);
v_lctx_2926_ = lean_ctor_get(v___y_2907_, 2);
v_localInstances_2927_ = lean_ctor_get(v___y_2907_, 3);
v_defEqCtx_x3f_2928_ = lean_ctor_get(v___y_2907_, 4);
v_synthPendingDepth_2929_ = lean_ctor_get(v___y_2907_, 5);
v_canUnfold_x3f_2930_ = lean_ctor_get(v___y_2907_, 6);
v_univApprox_2931_ = lean_ctor_get_uint8(v___y_2907_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2932_ = lean_ctor_get_uint8(v___y_2907_, sizeof(void*)*7 + 2);
v_cacheInferType_2933_ = lean_ctor_get_uint8(v___y_2907_, sizeof(void*)*7 + 3);
v___x_2934_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2923_);
v___x_2935_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___x_2936_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2935_, v___x_2918_, v_env_2917_, v_asyncMode_2921_);
lean_inc_ref(v_config_2923_);
v___x_2937_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2937_, 0, v_config_2923_);
lean_ctor_set_uint64(v___x_2937_, sizeof(void*)*1, v___x_2934_);
lean_inc(v_canUnfold_x3f_2930_);
lean_inc(v_synthPendingDepth_2929_);
lean_inc(v_defEqCtx_x3f_2928_);
lean_inc_ref(v_localInstances_2927_);
lean_inc_ref(v_lctx_2926_);
lean_inc(v_zetaDeltaSet_2925_);
v___x_2938_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v_zetaDeltaSet_2925_);
lean_ctor_set(v___x_2938_, 2, v_lctx_2926_);
lean_ctor_set(v___x_2938_, 3, v_localInstances_2927_);
lean_ctor_set(v___x_2938_, 4, v_defEqCtx_x3f_2928_);
lean_ctor_set(v___x_2938_, 5, v_synthPendingDepth_2929_);
lean_ctor_set(v___x_2938_, 6, v_canUnfold_x3f_2930_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*7, v_trackZetaDelta_2924_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*7 + 1, v_univApprox_2931_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2932_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*7 + 3, v_cacheInferType_2933_);
lean_inc_ref(v_t_2899_);
v___x_2939_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v___x_2936_, v_t_2899_, v___x_2938_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec_ref(v___x_2938_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; size_t v_sz_2942_; size_t v___x_2943_; lean_object* v___x_2944_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref(v___x_2939_);
v___x_2941_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_sz_2942_ = lean_array_size(v_a_2940_);
v___x_2943_ = ((size_t)0ULL);
v___x_2944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2899_, v_s_2900_, v_unificationHints_2912_, v_a_2940_, v_sz_2942_, v___x_2943_, v___x_2941_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v_a_2940_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2958_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2958_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2958_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_fst_2949_; 
v_fst_2949_ = lean_ctor_get(v_a_2945_, 0);
lean_inc(v_fst_2949_);
lean_dec(v_a_2945_);
if (lean_obj_tag(v_fst_2949_) == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_box(v___x_2915_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2950_);
v___x_2952_ = v___x_2947_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
else
{
lean_object* v_val_2954_; lean_object* v___x_2956_; 
v_val_2954_ = lean_ctor_get(v_fst_2949_, 0);
lean_inc(v_val_2954_);
lean_dec_ref(v_fst_2949_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v_val_2954_);
v___x_2956_ = v___x_2947_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_val_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
v_a_2959_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2944_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2944_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v_s_2900_);
lean_dec_ref(v_t_2899_);
v_a_2967_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2939_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2939_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_dec_ref(v_s_2900_);
lean_dec_ref(v_t_2899_);
v___x_2975_ = 0;
v___x_2976_ = lean_box(v___x_2975_);
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
return v___x_2977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___boxed(lean_object* v_t_2998_, lean_object* v_s_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_Meta_tryUnificationHints(v_t_2998_, v_s_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_);
lean_dec(v_a_3003_);
lean_dec_ref(v_a_3002_);
lean_dec(v_a_3001_);
lean_dec_ref(v_a_3000_);
return v_res_3005_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = lean_unsigned_to_nat(2674080740u);
v___x_3007_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3008_ = l_Lean_Name_num___override(v___x_3007_, v___x_3006_);
return v___x_3008_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3010_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3011_ = l_Lean_Name_str___override(v___x_3010_, v___x_3009_);
return v___x_3011_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3013_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3014_ = l_Lean_Name_str___override(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_unsigned_to_nat(2u);
v___x_3016_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3017_ = l_Lean_Name_num___override(v___x_3016_, v___x_3015_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3019_; uint8_t v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3019_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_3020_ = 0;
v___x_3021_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3022_ = l_Lean_registerTraceClass(v___x_3019_, v___x_3020_, v___x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
return v_res_3024_;
}
}
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_UnificationHint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedUnificationHints_default = _init_l_Lean_Meta_instInhabitedUnificationHints_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints_default);
l_Lean_Meta_instInhabitedUnificationHints = _init_l_Lean_Meta_instInhabitedUnificationHints();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config);
res = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_unificationHintExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_unificationHintExtension);
lean_dec_ref(res);
res = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_UnificationHint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_UnificationHint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_UnificationHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_UnificationHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_UnificationHint(builtin);
}
#ifdef __cplusplus
}
#endif
