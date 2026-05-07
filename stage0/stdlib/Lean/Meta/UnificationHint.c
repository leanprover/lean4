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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object*, lean_object*);
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
lean_object* v_es_399_; lean_object* v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; lean_object* v_j_404_; lean_object* v___x_405_; 
v_es_399_ = lean_ctor_get(v_x_396_, 0);
v___x_400_ = lean_box(2);
v___x_401_ = ((size_t)5ULL);
v___x_402_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_403_ = lean_usize_land(v_x_397_, v___x_402_);
v_j_404_ = lean_usize_to_nat(v___x_403_);
v___x_405_ = lean_array_get_borrowed(v___x_400_, v_es_399_, v_j_404_);
lean_dec(v_j_404_);
switch(lean_obj_tag(v___x_405_))
{
case 0:
{
lean_object* v_key_406_; lean_object* v_val_407_; uint8_t v___x_408_; 
v_key_406_ = lean_ctor_get(v___x_405_, 0);
v_val_407_ = lean_ctor_get(v___x_405_, 1);
v___x_408_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_398_, v_key_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_box(0);
return v___x_409_;
}
else
{
lean_object* v___x_410_; 
lean_inc(v_val_407_);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v_val_407_);
return v___x_410_;
}
}
case 1:
{
lean_object* v_node_411_; size_t v___x_412_; 
v_node_411_ = lean_ctor_get(v___x_405_, 0);
v___x_412_ = lean_usize_shift_right(v_x_397_, v___x_401_);
v_x_396_ = v_node_411_;
v_x_397_ = v___x_412_;
goto _start;
}
default: 
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
}
}
else
{
lean_object* v_ks_415_; lean_object* v_vs_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_ks_415_ = lean_ctor_get(v_x_396_, 0);
v_vs_416_ = lean_ctor_get(v_x_396_, 1);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_415_, v_vs_416_, v___x_417_, v_x_398_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
size_t v_x_2052__boxed_422_; lean_object* v_res_423_; 
v_x_2052__boxed_422_ = lean_unbox_usize(v_x_420_);
lean_dec(v_x_420_);
v_res_423_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_419_, v_x_2052__boxed_422_, v_x_421_);
lean_dec(v_x_421_);
lean_dec_ref(v_x_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
uint64_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v___x_426_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_425_);
v___x_427_ = lean_uint64_to_usize(v___x_426_);
v___x_428_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_424_, v___x_427_, v_x_425_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg___boxed(lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_x_429_, v_x_430_);
lean_dec(v_x_430_);
lean_dec_ref(v_x_429_);
return v_res_431_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_435_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2));
v___x_436_ = lean_unsigned_to_nat(23u);
v___x_437_ = lean_unsigned_to_nat(166u);
v___x_438_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1));
v___x_439_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0));
v___x_440_ = l_mkPanicMessageWithDecl(v___x_439_, v___x_438_, v___x_437_, v___x_436_, v___x_435_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(lean_object* v_d_441_, lean_object* v_keys_442_, lean_object* v_v_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_array_get_size(v_keys_442_);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_nat_dec_eq(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v_k_448_; lean_object* v___x_449_; 
v___x_447_ = lean_box(0);
v_k_448_ = lean_array_get_borrowed(v___x_447_, v_keys_442_, v___x_445_);
v___x_449_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_d_441_, v_k_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; lean_object* v_c_451_; lean_object* v___x_452_; 
v___x_450_ = lean_unsigned_to_nat(1u);
v_c_451_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_442_, v_v_443_, v___x_450_);
lean_inc(v_k_448_);
v___x_452_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_d_441_, v_k_448_, v_c_451_);
return v___x_452_;
}
else
{
lean_object* v_val_453_; lean_object* v___x_454_; lean_object* v_c_455_; lean_object* v___x_456_; 
v_val_453_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_val_453_);
lean_dec_ref(v___x_449_);
v___x_454_ = lean_unsigned_to_nat(1u);
v_c_455_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_442_, v_v_443_, v___x_454_, v_val_453_);
lean_inc(v_k_448_);
v___x_456_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_d_441_, v_k_448_, v_c_455_);
return v___x_456_;
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_v_443_);
lean_dec_ref(v_d_441_);
v___x_457_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3);
v___x_458_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3(v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___boxed(lean_object* v_d_459_, lean_object* v_keys_460_, lean_object* v_v_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_d_459_, v_keys_460_, v_v_461_);
lean_dec_ref(v_keys_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* v_hints_463_, lean_object* v_e_464_){
_start:
{
lean_object* v_keys_465_; lean_object* v_val_466_; lean_object* v___x_467_; 
v_keys_465_ = lean_ctor_get(v_e_464_, 0);
lean_inc_ref(v_keys_465_);
v_val_466_ = lean_ctor_get(v_e_464_, 1);
lean_inc(v_val_466_);
lean_dec_ref(v_e_464_);
v___x_467_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_hints_463_, v_keys_465_, v_val_466_);
lean_dec_ref(v_keys_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_00_u03b2_472_, v_x_473_, v_x_474_);
lean_dec(v_x_474_);
lean_dec_ref(v_x_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_x_477_, v_x_478_, v_x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, size_t v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_482_, v_x_483_, v_x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
size_t v_x_2182__boxed_490_; lean_object* v_res_491_; 
v_x_2182__boxed_490_ = lean_unbox_usize(v_x_488_);
lean_dec(v_x_488_);
v_res_491_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(v_00_u03b2_486_, v_x_487_, v_x_2182__boxed_490_, v_x_489_);
lean_dec(v_x_489_);
lean_dec_ref(v_x_487_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_492_, lean_object* v_x_493_, size_t v_x_494_, size_t v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_493_, v_x_494_, v_x_495_, v_x_496_, v_x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
size_t v_x_2193__boxed_505_; size_t v_x_2194__boxed_506_; lean_object* v_res_507_; 
v_x_2193__boxed_505_ = lean_unbox_usize(v_x_501_);
lean_dec(v_x_501_);
v_x_2194__boxed_506_ = lean_unbox_usize(v_x_502_);
lean_dec(v_x_502_);
v_res_507_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3(v_00_u03b2_499_, v_x_500_, v_x_2193__boxed_505_, v_x_2194__boxed_506_, v_x_503_, v_x_504_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_508_, lean_object* v_keys_509_, lean_object* v_vals_510_, lean_object* v_heq_511_, lean_object* v_i_512_, lean_object* v_k_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_509_, v_vals_510_, v_i_512_, v_k_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_515_, lean_object* v_keys_516_, lean_object* v_vals_517_, lean_object* v_heq_518_, lean_object* v_i_519_, lean_object* v_k_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_515_, v_keys_516_, v_vals_517_, v_heq_518_, v_i_519_, v_k_520_);
lean_dec(v_k_520_);
lean_dec_ref(v_vals_517_);
lean_dec_ref(v_keys_516_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_522_, lean_object* v_n_523_, lean_object* v_k_524_, lean_object* v_v_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(v_n_523_, v_k_524_, v_v_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_527_, size_t v_depth_528_, lean_object* v_keys_529_, lean_object* v_vals_530_, lean_object* v_heq_531_, lean_object* v_i_532_, lean_object* v_entries_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_528_, v_keys_529_, v_vals_530_, v_i_532_, v_entries_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_535_, lean_object* v_depth_536_, lean_object* v_keys_537_, lean_object* v_vals_538_, lean_object* v_heq_539_, lean_object* v_i_540_, lean_object* v_entries_541_){
_start:
{
size_t v_depth_boxed_542_; lean_object* v_res_543_; 
v_depth_boxed_542_ = lean_unbox_usize(v_depth_536_);
lean_dec(v_depth_536_);
v_res_543_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_535_, v_depth_boxed_542_, v_keys_537_, v_vals_538_, v_heq_539_, v_i_540_, v_entries_541_);
lean_dec_ref(v_vals_538_);
lean_dec_ref(v_keys_537_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12(lean_object* v_x_544_, lean_object* v_keys_545_, lean_object* v_v_546_, lean_object* v_k_547_, lean_object* v_as_548_, lean_object* v_k_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_544_, v_keys_545_, v_v_546_, v_k_547_, v_as_548_, v_k_549_, v_x_550_, v_x_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_x_555_, lean_object* v_keys_556_, lean_object* v_v_557_, lean_object* v_k_558_, lean_object* v_as_559_, lean_object* v_k_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12(v_x_555_, v_keys_556_, v_v_557_, v_k_558_, v_as_559_, v_k_560_, v_x_561_, v_x_562_, v_x_563_, v_x_564_);
lean_dec_ref(v_k_560_);
lean_dec_ref(v_keys_556_);
lean_dec(v_x_555_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_567_, v_x_568_, v_x_569_, v_x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object* v_x_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v_a_573_);
lean_inc_ref_n(v___x_574_, 2);
v___x_575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
lean_ctor_set(v___x_575_, 2, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_x_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v_x_576_, v_a_577_);
lean_dec_ref(v_x_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object* v___y_579_){
_start:
{
lean_inc_ref(v___y_579_);
return v___y_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v___y_580_);
lean_dec_ref(v___y_580_);
return v_res_581_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_592_; lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___f_592_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___f_593_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_594_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___x_595_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_596_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
lean_ctor_set(v___x_597_, 2, v___x_594_);
lean_ctor_set(v___x_597_, 3, v___f_593_);
lean_ctor_set(v___x_597_, 4, v___f_592_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_);
v___x_600_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
return v_res_602_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2));
v___x_608_ = l_Lean_stringToMessageData(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object* v_e_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1));
v___x_611_ = lean_unsigned_to_nat(3u);
v___x_612_ = l_Lean_Expr_isAppOfArity(v_e_609_, v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_613_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3);
v___x_614_ = l_Lean_indentExpr(v_e_609_);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_617_ = l_Lean_Expr_appFn_x21(v_e_609_);
v___x_618_ = l_Lean_Expr_appArg_x21(v___x_617_);
lean_dec_ref(v___x_617_);
v___x_619_ = l_Lean_Expr_appArg_x21(v_e_609_);
lean_dec_ref(v_e_609_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object* v_e_625_, lean_object* v_cs_626_){
_start:
{
if (lean_obj_tag(v_e_625_) == 7)
{
lean_object* v_binderType_627_; lean_object* v_body_628_; lean_object* v___x_629_; 
v_binderType_627_ = lean_ctor_get(v_e_625_, 1);
v_body_628_ = lean_ctor_get(v_e_625_, 2);
lean_inc_ref(v_binderType_627_);
v___x_629_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_binderType_627_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_e_625_);
lean_dec_ref(v_cs_626_);
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_651_; 
v_a_638_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_651_ == 0)
{
v___x_640_ = v___x_629_;
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_629_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___x_642_; 
v___x_642_ = l_Lean_Expr_hasLooseBVars(v_body_628_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_inc_ref(v_body_628_);
lean_del_object(v___x_640_);
lean_dec_ref(v_e_625_);
v___x_643_ = lean_array_push(v_cs_626_, v_a_638_);
v_e_625_ = v_body_628_;
v_cs_626_ = v___x_643_;
goto _start;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
lean_dec(v_a_638_);
lean_dec_ref(v_cs_626_);
v___x_645_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1);
v___x_646_ = l_Lean_indentExpr(v_e_625_);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 0);
lean_ctor_set(v___x_640_, 0, v___x_647_);
v___x_649_ = v___x_640_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
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
else
{
lean_object* v___x_652_; 
v___x_652_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_e_625_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v_cs_626_);
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_670_; 
v_a_661_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_670_ == 0)
{
v___x_663_ = v___x_652_;
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_652_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_665_ = lean_array_to_list(v_cs_626_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_a_661_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_666_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object* v_e_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0));
v___x_675_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(v_e_673_, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(lean_object* v_msgData_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; lean_object* v_env_683_; lean_object* v___x_684_; lean_object* v_mctx_685_; lean_object* v_lctx_686_; lean_object* v_options_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_682_ = lean_st_ref_get(v___y_680_);
v_env_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc_ref(v_env_683_);
lean_dec(v___x_682_);
v___x_684_ = lean_st_ref_get(v___y_678_);
v_mctx_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_ref(v_mctx_685_);
lean_dec(v___x_684_);
v_lctx_686_ = lean_ctor_get(v___y_677_, 2);
v_options_687_ = lean_ctor_get(v___y_679_, 2);
lean_inc_ref(v_options_687_);
lean_inc_ref(v_lctx_686_);
v___x_688_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_688_, 0, v_env_683_);
lean_ctor_set(v___x_688_, 1, v_mctx_685_);
lean_ctor_set(v___x_688_, 2, v_lctx_686_);
lean_ctor_set(v___x_688_, 3, v_options_687_);
v___x_689_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_msgData_676_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object* v_msgData_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msgData_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_ref_704_; lean_object* v___x_705_; lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_714_; 
v_ref_704_ = lean_ctor_get(v___y_701_, 5);
v___x_705_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_714_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
lean_inc(v_ref_704_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_ref_704_);
lean_ctor_set(v___x_710_, 1, v_a_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 1);
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg___boxed(lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_721_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2));
v___x_727_ = l_Lean_stringToMessageData(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(lean_object* v_as_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
if (lean_obj_tag(v_as_728_) == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(0);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v_head_736_; lean_object* v_tail_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_771_; 
v_head_736_ = lean_ctor_get(v_as_728_, 0);
v_tail_737_ = lean_ctor_get(v_as_728_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_as_728_);
if (v_isSharedCheck_771_ == 0)
{
v___x_739_ = v_as_728_;
v_isShared_740_ = v_isSharedCheck_771_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_tail_737_);
lean_inc(v_head_736_);
lean_dec(v_as_728_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_771_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_lhs_741_; lean_object* v_rhs_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_770_; 
v_lhs_741_ = lean_ctor_get(v_head_736_, 0);
v_rhs_742_ = lean_ctor_get(v_head_736_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_head_736_);
if (v_isSharedCheck_770_ == 0)
{
v___x_744_ = v_head_736_;
v_isShared_745_ = v_isSharedCheck_770_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_rhs_742_);
lean_inc(v_lhs_741_);
lean_dec(v_head_736_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_770_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; 
lean_inc_ref(v_rhs_742_);
lean_inc_ref(v_lhs_741_);
v___x_746_ = l_Lean_Meta_isExprDefEq(v_lhs_741_, v_rhs_742_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; uint8_t v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref(v___x_746_);
v___x_748_ = lean_unbox(v_a_747_);
lean_dec(v_a_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
lean_dec(v_tail_737_);
v___x_749_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1);
v___x_750_ = l_Lean_indentExpr(v_lhs_741_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 7);
lean_ctor_set(v___x_744_, 1, v___x_750_);
lean_ctor_set(v___x_744_, 0, v___x_749_);
v___x_752_ = v___x_744_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_750_);
v___x_752_ = v_reuseFailAlloc_760_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 7);
lean_ctor_set(v___x_739_, 1, v___x_753_);
lean_ctor_set(v___x_739_, 0, v___x_752_);
v___x_755_ = v___x_739_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = l_Lean_indentExpr(v_rhs_742_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_757_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
return v___x_758_;
}
}
}
else
{
lean_del_object(v___x_744_);
lean_dec_ref(v_rhs_742_);
lean_dec_ref(v_lhs_741_);
lean_del_object(v___x_739_);
v_as_728_ = v_tail_737_;
goto _start;
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_del_object(v___x_744_);
lean_dec_ref(v_rhs_742_);
lean_dec_ref(v_lhs_741_);
lean_del_object(v___x_739_);
lean_dec(v_tail_737_);
v_a_762_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_746_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_746_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___boxed(lean_object* v_as_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_as_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_778_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object* v_hint_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_pattern_788_; lean_object* v_constraints_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_831_; 
v_pattern_788_ = lean_ctor_get(v_hint_782_, 0);
v_constraints_789_ = lean_ctor_get(v_hint_782_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_hint_782_);
if (v_isSharedCheck_831_ == 0)
{
v___x_791_ = v_hint_782_;
v_isShared_792_ = v_isSharedCheck_831_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_constraints_789_);
lean_inc(v_pattern_788_);
lean_dec(v_hint_782_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_831_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; 
v___x_793_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_constraints_789_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_lhs_794_; lean_object* v_rhs_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v___x_793_);
v_lhs_794_ = lean_ctor_get(v_pattern_788_, 0);
v_rhs_795_ = lean_ctor_get(v_pattern_788_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_pattern_788_);
if (v_isSharedCheck_830_ == 0)
{
v___x_797_ = v_pattern_788_;
v_isShared_798_ = v_isSharedCheck_830_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_rhs_795_);
lean_inc(v_lhs_794_);
lean_dec(v_pattern_788_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_830_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; 
lean_inc_ref(v_rhs_795_);
lean_inc_ref(v_lhs_794_);
v___x_799_ = l_Lean_Meta_isExprDefEq(v_lhs_794_, v_rhs_795_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_821_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_821_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_821_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_821_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
uint8_t v___x_804_; 
v___x_804_ = lean_unbox(v_a_800_);
lean_dec(v_a_800_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
lean_del_object(v___x_802_);
v___x_805_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1);
v___x_806_ = l_Lean_indentExpr(v_lhs_794_);
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 7);
lean_ctor_set(v___x_797_, 1, v___x_806_);
lean_ctor_set(v___x_797_, 0, v___x_805_);
v___x_808_ = v___x_797_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_816_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 7);
lean_ctor_set(v___x_791_, 1, v___x_809_);
lean_ctor_set(v___x_791_, 0, v___x_808_);
v___x_811_ = v___x_791_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = l_Lean_indentExpr(v_rhs_795_);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_813_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
return v___x_814_;
}
}
}
else
{
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_del_object(v___x_797_);
lean_dec_ref(v_rhs_795_);
lean_dec_ref(v_lhs_794_);
lean_del_object(v___x_791_);
v___x_817_ = lean_box(0);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_817_);
v___x_819_ = v___x_802_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_del_object(v___x_797_);
lean_dec_ref(v_rhs_795_);
lean_dec_ref(v_lhs_794_);
lean_del_object(v___x_791_);
v_a_822_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_799_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_799_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
else
{
lean_del_object(v___x_791_);
lean_dec_ref(v_pattern_788_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object* v_hint_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_hint_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object* v_00_u03b1_839_, lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object* v_00_u03b1_847_, lean_object* v_msg_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(v_00_u03b1_847_, v_msg_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
return v_res_854_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_855_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_861_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
lean_ctor_set(v___x_861_, 2, v___x_860_);
lean_ctor_set(v___x_861_, 3, v___x_860_);
lean_ctor_set(v___x_861_, 4, v___x_860_);
lean_ctor_set(v___x_861_, 5, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(lean_object* v_ext_862_, lean_object* v_b_863_, uint8_t v_kind_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_currNamespace_869_; lean_object* v___x_870_; lean_object* v_env_871_; lean_object* v_nextMacroScope_872_; lean_object* v_ngen_873_; lean_object* v_auxDeclNGen_874_; lean_object* v_traceState_875_; lean_object* v_messages_876_; lean_object* v_infoState_877_; lean_object* v_snapshotTasks_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_905_; 
v_currNamespace_869_ = lean_ctor_get(v___y_866_, 6);
v___x_870_ = lean_st_ref_take(v___y_867_);
v_env_871_ = lean_ctor_get(v___x_870_, 0);
v_nextMacroScope_872_ = lean_ctor_get(v___x_870_, 1);
v_ngen_873_ = lean_ctor_get(v___x_870_, 2);
v_auxDeclNGen_874_ = lean_ctor_get(v___x_870_, 3);
v_traceState_875_ = lean_ctor_get(v___x_870_, 4);
v_messages_876_ = lean_ctor_get(v___x_870_, 6);
v_infoState_877_ = lean_ctor_get(v___x_870_, 7);
v_snapshotTasks_878_ = lean_ctor_get(v___x_870_, 8);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_870_, 5);
lean_dec(v_unused_906_);
v___x_880_ = v___x_870_;
v_isShared_881_ = v_isSharedCheck_905_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_snapshotTasks_878_);
lean_inc(v_infoState_877_);
lean_inc(v_messages_876_);
lean_inc(v_traceState_875_);
lean_inc(v_auxDeclNGen_874_);
lean_inc(v_ngen_873_);
lean_inc(v_nextMacroScope_872_);
lean_inc(v_env_871_);
lean_dec(v___x_870_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_905_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
lean_inc(v_currNamespace_869_);
v___x_882_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_871_, v_ext_862_, v_b_863_, v_kind_864_, v_currNamespace_869_);
v___x_883_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 5, v___x_883_);
lean_ctor_set(v___x_880_, 0, v___x_882_);
v___x_885_ = v___x_880_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_nextMacroScope_872_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_ngen_873_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_auxDeclNGen_874_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_traceState_875_);
lean_ctor_set(v_reuseFailAlloc_904_, 5, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_904_, 6, v_messages_876_);
lean_ctor_set(v_reuseFailAlloc_904_, 7, v_infoState_877_);
lean_ctor_set(v_reuseFailAlloc_904_, 8, v_snapshotTasks_878_);
v___x_885_ = v_reuseFailAlloc_904_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_mctx_888_; lean_object* v_zetaDeltaFVarIds_889_; lean_object* v_postponed_890_; lean_object* v_diag_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_902_; 
v___x_886_ = lean_st_ref_set(v___y_867_, v___x_885_);
v___x_887_ = lean_st_ref_take(v___y_865_);
v_mctx_888_ = lean_ctor_get(v___x_887_, 0);
v_zetaDeltaFVarIds_889_ = lean_ctor_get(v___x_887_, 2);
v_postponed_890_ = lean_ctor_get(v___x_887_, 3);
v_diag_891_ = lean_ctor_get(v___x_887_, 4);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_887_, 1);
lean_dec(v_unused_903_);
v___x_893_ = v___x_887_;
v_isShared_894_ = v_isSharedCheck_902_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_diag_891_);
lean_inc(v_postponed_890_);
lean_inc(v_zetaDeltaFVarIds_889_);
lean_inc(v_mctx_888_);
lean_dec(v___x_887_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_902_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v___x_895_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_mctx_888_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_zetaDeltaFVarIds_889_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_postponed_890_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_diag_891_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_st_ref_set(v___y_865_, v___x_897_);
v___x_899_ = lean_box(0);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(lean_object* v_ext_907_, lean_object* v_b_908_, lean_object* v_kind_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
uint8_t v_kind_boxed_914_; lean_object* v_res_915_; 
v_kind_boxed_914_ = lean_unbox(v_kind_909_);
v_res_915_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_907_, v_b_908_, v_kind_boxed_914_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object* v_00_u03b1_916_, lean_object* v_00_u03b2_917_, lean_object* v_00_u03c3_918_, lean_object* v_ext_919_, lean_object* v_b_920_, uint8_t v_kind_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_919_, v_b_920_, v_kind_921_, v___y_923_, v___y_924_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_00_u03c3_930_, lean_object* v_ext_931_, lean_object* v_b_932_, lean_object* v_kind_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
uint8_t v_kind_boxed_939_; lean_object* v_res_940_; 
v_kind_boxed_939_ = lean_unbox(v_kind_933_);
v_res_940_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(v_00_u03b1_928_, v_00_u03b2_929_, v_00_u03c3_930_, v_ext_931_, v_b_932_, v_kind_boxed_939_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(lean_object* v_k_941_, uint8_t v_allowLevelAssignments_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_942_, v_k_941_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_948_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_948_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(lean_object* v_k_965_, lean_object* v_allowLevelAssignments_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_972_; lean_object* v_res_973_; 
v_allowLevelAssignments_boxed_972_ = lean_unbox(v_allowLevelAssignments_966_);
v_res_973_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_965_, v_allowLevelAssignments_boxed_972_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(lean_object* v_00_u03b1_974_, lean_object* v_k_975_, uint8_t v_allowLevelAssignments_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_975_, v_allowLevelAssignments_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(lean_object* v_00_u03b1_983_, lean_object* v_k_984_, lean_object* v_allowLevelAssignments_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_991_; lean_object* v_res_992_; 
v_allowLevelAssignments_boxed_991_ = lean_unbox(v_allowLevelAssignments_985_);
v_res_992_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(v_00_u03b1_983_, v_k_984_, v_allowLevelAssignments_boxed_991_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
lean_ctor_set(v___x_998_, 2, v___x_997_);
lean_ctor_set(v___x_998_, 3, v___x_997_);
lean_ctor_set(v___x_998_, 4, v___x_996_);
lean_ctor_set(v___x_998_, 5, v___x_996_);
lean_ctor_set(v___x_998_, 6, v___x_996_);
lean_ctor_set(v___x_998_, 7, v___x_996_);
lean_ctor_set(v___x_998_, 8, v___x_996_);
lean_ctor_set(v___x_998_, 9, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_unsigned_to_nat(32u);
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_999_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1002_ = ((size_t)5ULL);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_unsigned_to_nat(32u);
v___x_1005_ = lean_mk_empty_array_with_capacity(v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1007_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
lean_ctor_set(v___x_1007_, 2, v___x_1003_);
lean_ctor_set(v___x_1007_, 3, v___x_1003_);
lean_ctor_set_usize(v___x_1007_, 4, v___x_1002_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = lean_box(1);
v___x_1009_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
lean_ctor_set(v___x_1011_, 2, v___x_1008_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1033_, lean_object* v_declHint_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v_env_1038_; uint8_t v___x_1039_; 
v___x_1037_ = lean_st_ref_get(v___y_1035_);
v_env_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc_ref(v_env_1038_);
lean_dec(v___x_1037_);
v___x_1039_ = l_Lean_Name_isAnonymous(v_declHint_1034_);
if (v___x_1039_ == 0)
{
uint8_t v_isExporting_1040_; 
v_isExporting_1040_ = lean_ctor_get_uint8(v_env_1038_, sizeof(void*)*8);
if (v_isExporting_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_msg_1033_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
lean_inc_ref(v_env_1038_);
v___x_1042_ = l_Lean_Environment_setExporting(v_env_1038_, v___x_1039_);
lean_inc(v_declHint_1034_);
lean_inc_ref(v___x_1042_);
v___x_1043_ = l_Lean_Environment_contains(v___x_1042_, v_declHint_1034_, v_isExporting_1040_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
lean_dec_ref(v___x_1042_);
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v_msg_1033_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_c_1050_; lean_object* v___x_1051_; 
v___x_1045_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1047_ = l_Lean_Options_empty;
v___x_1048_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1042_);
lean_ctor_set(v___x_1048_, 1, v___x_1045_);
lean_ctor_set(v___x_1048_, 2, v___x_1046_);
lean_ctor_set(v___x_1048_, 3, v___x_1047_);
lean_inc(v_declHint_1034_);
v___x_1049_ = l_Lean_MessageData_ofConstName(v_declHint_1034_, v___x_1039_);
v_c_1050_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1050_, 0, v___x_1048_);
lean_ctor_set(v_c_1050_, 1, v___x_1049_);
v___x_1051_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1038_, v_declHint_1034_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_c_1050_);
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_MessageData_note(v___x_1055_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_msg_1033_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1094_; 
v_val_1059_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1061_ = v___x_1051_;
v_isShared_1062_ = v_isSharedCheck_1094_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v___x_1051_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1094_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_mod_1066_; uint8_t v___x_1067_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = l_Lean_Environment_header(v_env_1038_);
lean_dec_ref(v_env_1038_);
v___x_1065_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1064_);
v_mod_1066_ = lean_array_get(v___x_1063_, v___x_1065_, v_val_1059_);
lean_dec(v_val_1059_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l_Lean_isPrivateName(v_declHint_1034_);
lean_dec(v_declHint_1034_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_c_1050_);
v___x_1070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = l_Lean_MessageData_ofName(v_mod_1066_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_MessageData_note(v___x_1075_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_msg_1033_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1077_);
v___x_1079_ = v___x_1061_;
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
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1081_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v_c_1050_);
v___x_1083_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_MessageData_ofName(v_mod_1066_);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_Lean_MessageData_note(v___x_1088_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_msg_1033_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1090_);
v___x_1092_ = v___x_1061_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
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
}
}
}
else
{
lean_object* v___x_1095_; 
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_msg_1033_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1096_, lean_object* v_declHint_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1096_, v_declHint_1097_, v___y_1098_);
lean_dec(v___y_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object* v_msg_1101_, lean_object* v_declHint_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1118_; 
v___x_1108_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1101_, v_declHint_1102_, v___y_1106_);
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1113_ = l_Lean_unknownIdentifierMessageTag;
v___x_1114_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_a_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1114_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1119_, lean_object* v_declHint_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1119_, v_declHint_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1127_, lean_object* v_msg_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_fileName_1134_; lean_object* v_fileMap_1135_; lean_object* v_options_1136_; lean_object* v_currRecDepth_1137_; lean_object* v_maxRecDepth_1138_; lean_object* v_ref_1139_; lean_object* v_currNamespace_1140_; lean_object* v_openDecls_1141_; lean_object* v_initHeartbeats_1142_; lean_object* v_maxHeartbeats_1143_; lean_object* v_quotContext_1144_; lean_object* v_currMacroScope_1145_; uint8_t v_diag_1146_; lean_object* v_cancelTk_x3f_1147_; uint8_t v_suppressElabErrors_1148_; lean_object* v_inheritedTraceOptions_1149_; lean_object* v_ref_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_fileName_1134_ = lean_ctor_get(v___y_1131_, 0);
v_fileMap_1135_ = lean_ctor_get(v___y_1131_, 1);
v_options_1136_ = lean_ctor_get(v___y_1131_, 2);
v_currRecDepth_1137_ = lean_ctor_get(v___y_1131_, 3);
v_maxRecDepth_1138_ = lean_ctor_get(v___y_1131_, 4);
v_ref_1139_ = lean_ctor_get(v___y_1131_, 5);
v_currNamespace_1140_ = lean_ctor_get(v___y_1131_, 6);
v_openDecls_1141_ = lean_ctor_get(v___y_1131_, 7);
v_initHeartbeats_1142_ = lean_ctor_get(v___y_1131_, 8);
v_maxHeartbeats_1143_ = lean_ctor_get(v___y_1131_, 9);
v_quotContext_1144_ = lean_ctor_get(v___y_1131_, 10);
v_currMacroScope_1145_ = lean_ctor_get(v___y_1131_, 11);
v_diag_1146_ = lean_ctor_get_uint8(v___y_1131_, sizeof(void*)*14);
v_cancelTk_x3f_1147_ = lean_ctor_get(v___y_1131_, 12);
v_suppressElabErrors_1148_ = lean_ctor_get_uint8(v___y_1131_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1149_ = lean_ctor_get(v___y_1131_, 13);
v_ref_1150_ = l_Lean_replaceRef(v_ref_1127_, v_ref_1139_);
lean_inc_ref(v_inheritedTraceOptions_1149_);
lean_inc(v_cancelTk_x3f_1147_);
lean_inc(v_currMacroScope_1145_);
lean_inc(v_quotContext_1144_);
lean_inc(v_maxHeartbeats_1143_);
lean_inc(v_initHeartbeats_1142_);
lean_inc(v_openDecls_1141_);
lean_inc(v_currNamespace_1140_);
lean_inc(v_maxRecDepth_1138_);
lean_inc(v_currRecDepth_1137_);
lean_inc_ref(v_options_1136_);
lean_inc_ref(v_fileMap_1135_);
lean_inc_ref(v_fileName_1134_);
v___x_1151_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1151_, 0, v_fileName_1134_);
lean_ctor_set(v___x_1151_, 1, v_fileMap_1135_);
lean_ctor_set(v___x_1151_, 2, v_options_1136_);
lean_ctor_set(v___x_1151_, 3, v_currRecDepth_1137_);
lean_ctor_set(v___x_1151_, 4, v_maxRecDepth_1138_);
lean_ctor_set(v___x_1151_, 5, v_ref_1150_);
lean_ctor_set(v___x_1151_, 6, v_currNamespace_1140_);
lean_ctor_set(v___x_1151_, 7, v_openDecls_1141_);
lean_ctor_set(v___x_1151_, 8, v_initHeartbeats_1142_);
lean_ctor_set(v___x_1151_, 9, v_maxHeartbeats_1143_);
lean_ctor_set(v___x_1151_, 10, v_quotContext_1144_);
lean_ctor_set(v___x_1151_, 11, v_currMacroScope_1145_);
lean_ctor_set(v___x_1151_, 12, v_cancelTk_x3f_1147_);
lean_ctor_set(v___x_1151_, 13, v_inheritedTraceOptions_1149_);
lean_ctor_set_uint8(v___x_1151_, sizeof(void*)*14, v_diag_1146_);
lean_ctor_set_uint8(v___x_1151_, sizeof(void*)*14 + 1, v_suppressElabErrors_1148_);
v___x_1152_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_1128_, v___y_1129_, v___y_1130_, v___x_1151_, v___y_1132_);
lean_dec_ref(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1153_, lean_object* v_msg_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1153_, v_msg_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v_ref_1153_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_ref_1161_, lean_object* v_msg_1162_, lean_object* v_declHint_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v_a_1170_; lean_object* v___x_1171_; 
v___x_1169_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1162_, v_declHint_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1161_, v_a_1170_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1172_, lean_object* v_msg_1173_, lean_object* v_declHint_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1172_, v_msg_1173_, v_declHint_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v_ref_1172_);
return v_res_1180_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1183_ = l_Lean_stringToMessageData(v___x_1182_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1186_ = l_Lean_stringToMessageData(v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1187_, lean_object* v_constName_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1194_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1195_ = 0;
lean_inc(v_constName_1188_);
v___x_1196_ = l_Lean_MessageData_ofConstName(v_constName_1188_, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1194_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1187_, v___x_1199_, v_constName_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1201_, lean_object* v_constName_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1201_, v_constName_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v_ref_1201_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(lean_object* v_constName_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_ref_1215_; lean_object* v___x_1216_; 
v_ref_1215_ = lean_ctor_get(v___y_1212_, 5);
v___x_1216_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1215_, v_constName_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(lean_object* v_constName_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v_env_1231_; uint8_t v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = lean_st_ref_get(v___y_1228_);
v_env_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_ref(v_env_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = 0;
lean_inc(v_constName_1224_);
v___x_1233_ = l_Lean_Environment_find_x3f(v_env_1231_, v_constName_1224_, v___x_1232_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
return v___x_1234_;
}
else
{
lean_object* v_val_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_constName_1224_);
v_val_1235_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1233_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_val_1235_);
lean_dec(v___x_1233_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 0);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_val_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(lean_object* v_constName_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_constName_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1249_;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_Meta_addUnificationHint___lam__0___closed__0));
v___x_1252_ = l_Lean_stringToMessageData(v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object* v_declName_1253_, uint8_t v_kind_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
lean_inc(v_declName_1253_);
v___x_1260_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_declName_1253_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = 0;
v___x_1263_ = l_Lean_ConstantInfo_value_x3f(v_a_1261_, v___x_1262_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_declName_1253_);
v___x_1264_ = lean_obj_once(&l_Lean_Meta_addUnificationHint___lam__0___closed__1, &l_Lean_Meta_addUnificationHint___lam__0___closed__1_once, _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1);
v___x_1265_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_1264_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1265_;
}
else
{
lean_object* v_val_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_val_1266_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1266_);
lean_dec_ref(v___x_1263_);
v___x_1267_ = lean_box(0);
v___x_1268_ = l_Lean_Meta_lambdaMetaTelescope(v_val_1266_, v___x_1267_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v_val_1266_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v_snd_1270_; lean_object* v_snd_1271_; lean_object* v___x_1272_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref(v___x_1268_);
v_snd_1270_ = lean_ctor_get(v_a_1269_, 1);
lean_inc(v_snd_1270_);
lean_dec(v_a_1269_);
v_snd_1271_ = lean_ctor_get(v_snd_1270_, 1);
lean_inc(v_snd_1271_);
lean_dec(v_snd_1270_);
v___x_1272_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_1271_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
lean_dec(v_declName_1253_);
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_a_1273_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1274_;
}
else
{
lean_object* v_a_1275_; lean_object* v_pattern_1276_; lean_object* v_lhs_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1312_; 
v_a_1275_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1272_);
v_pattern_1276_ = lean_ctor_get(v_a_1275_, 0);
lean_inc_ref(v_pattern_1276_);
v_lhs_1277_ = lean_ctor_get(v_pattern_1276_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_pattern_1276_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_pattern_1276_, 1);
lean_dec(v_unused_1313_);
v___x_1279_ = v_pattern_1276_;
v_isShared_1280_ = v_isSharedCheck_1312_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_lhs_1277_);
lean_dec(v_pattern_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1312_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v_config_1282_; uint8_t v_trackZetaDelta_1283_; lean_object* v_zetaDeltaSet_1284_; lean_object* v_lctx_1285_; lean_object* v_localInstances_1286_; lean_object* v_defEqCtx_x3f_1287_; lean_object* v_synthPendingDepth_1288_; lean_object* v_canUnfold_x3f_1289_; uint8_t v_univApprox_1290_; uint8_t v_inTypeClassResolution_1291_; uint8_t v_cacheInferType_1292_; uint64_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1281_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_1282_ = lean_ctor_get(v___x_1281_, 0);
v_trackZetaDelta_1283_ = lean_ctor_get_uint8(v___y_1255_, sizeof(void*)*7);
v_zetaDeltaSet_1284_ = lean_ctor_get(v___y_1255_, 1);
v_lctx_1285_ = lean_ctor_get(v___y_1255_, 2);
v_localInstances_1286_ = lean_ctor_get(v___y_1255_, 3);
v_defEqCtx_x3f_1287_ = lean_ctor_get(v___y_1255_, 4);
v_synthPendingDepth_1288_ = lean_ctor_get(v___y_1255_, 5);
v_canUnfold_x3f_1289_ = lean_ctor_get(v___y_1255_, 6);
v_univApprox_1290_ = lean_ctor_get_uint8(v___y_1255_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1291_ = lean_ctor_get_uint8(v___y_1255_, sizeof(void*)*7 + 2);
v_cacheInferType_1292_ = lean_ctor_get_uint8(v___y_1255_, sizeof(void*)*7 + 3);
v___x_1293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1282_);
lean_inc_ref(v_config_1282_);
v___x_1294_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1294_, 0, v_config_1282_);
lean_ctor_set_uint64(v___x_1294_, sizeof(void*)*1, v___x_1293_);
lean_inc(v_canUnfold_x3f_1289_);
lean_inc(v_synthPendingDepth_1288_);
lean_inc(v_defEqCtx_x3f_1287_);
lean_inc_ref(v_localInstances_1286_);
lean_inc_ref(v_lctx_1285_);
lean_inc(v_zetaDeltaSet_1284_);
v___x_1295_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v_zetaDeltaSet_1284_);
lean_ctor_set(v___x_1295_, 2, v_lctx_1285_);
lean_ctor_set(v___x_1295_, 3, v_localInstances_1286_);
lean_ctor_set(v___x_1295_, 4, v_defEqCtx_x3f_1287_);
lean_ctor_set(v___x_1295_, 5, v_synthPendingDepth_1288_);
lean_ctor_set(v___x_1295_, 6, v_canUnfold_x3f_1289_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*7, v_trackZetaDelta_1283_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*7 + 1, v_univApprox_1290_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1291_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*7 + 3, v_cacheInferType_1292_);
v___x_1296_ = l_Lean_Meta_DiscrTree_mkPath(v_lhs_1277_, v___x_1262_, v___x_1295_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec_ref(v___x_1295_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_a_1275_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_dec_ref(v___x_1298_);
v___x_1299_ = l_Lean_Meta_unificationHintExtension;
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v_declName_1253_);
lean_ctor_set(v___x_1279_, 0, v_a_1297_);
v___x_1301_ = v___x_1279_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_declName_1253_);
v___x_1301_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v___x_1299_, v___x_1301_, v_kind_1254_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1302_;
}
}
else
{
lean_dec(v_a_1297_);
lean_del_object(v___x_1279_);
lean_dec(v_declName_1253_);
return v___x_1298_;
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_del_object(v___x_1279_);
lean_dec(v_a_1275_);
lean_dec(v_declName_1253_);
v_a_1304_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1296_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1296_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v_declName_1253_);
v_a_1314_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1268_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1268_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v_declName_1253_);
v_a_1322_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1260_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1260_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object* v_declName_1330_, lean_object* v_kind_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v_kind_boxed_1337_; lean_object* v_res_1338_; 
v_kind_boxed_1337_ = lean_unbox(v_kind_1331_);
v_res_1338_ = l_Lean_Meta_addUnificationHint___lam__0(v_declName_1330_, v_kind_boxed_1337_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* v_declName_1339_, uint8_t v_kind_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v___f_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1346_ = lean_box(v_kind_1340_);
v___f_1347_ = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1347_, 0, v_declName_1339_);
lean_closure_set(v___f_1347_, 1, v___x_1346_);
v___x_1348_ = 0;
v___x_1349_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v___f_1347_, v___x_1348_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* v_declName_1350_, lean_object* v_kind_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
uint8_t v_kind_boxed_1357_; lean_object* v_res_1358_; 
v_kind_boxed_1357_ = lean_unbox(v_kind_1351_);
v_res_1358_ = l_Lean_Meta_addUnificationHint(v_declName_1350_, v_kind_boxed_1357_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object* v_00_u03b1_1359_, lean_object* v_constName_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_constName_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(v_00_u03b1_1367_, v_constName_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1375_, lean_object* v_ref_1376_, lean_object* v_constName_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1376_, v_constName_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_ref_1385_, lean_object* v_constName_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(v_00_u03b1_1384_, v_ref_1385_, v_constName_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v_ref_1385_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_1393_, lean_object* v_ref_1394_, lean_object* v_msg_1395_, lean_object* v_declHint_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1394_, v_msg_1395_, v_declHint_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_ref_1404_, lean_object* v_msg_1405_, lean_object* v_declHint_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(v_00_u03b1_1403_, v_ref_1404_, v_msg_1405_, v_declHint_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v_ref_1404_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1413_, lean_object* v_declHint_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1413_, v_declHint_1414_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1421_, lean_object* v_declHint_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(v_msg_1421_, v_declHint_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1429_, lean_object* v_ref_1430_, lean_object* v_msg_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1430_, v_msg_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1438_, lean_object* v_ref_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(v_00_u03b1_1438_, v_ref_1439_, v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v_ref_1439_);
return v_res_1446_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1453_; uint64_t v___x_1454_; 
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1454_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1456_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1457_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
lean_ctor_set_uint64(v___x_1457_, sizeof(void*)*1, v___x_1455_);
return v___x_1457_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1458_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1462_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
lean_ctor_set(v___x_1462_, 2, v___x_1461_);
lean_ctor_set(v___x_1462_, 3, v___x_1461_);
lean_ctor_set(v___x_1462_, 4, v___x_1461_);
lean_ctor_set(v___x_1462_, 5, v___x_1461_);
return v___x_1462_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
lean_ctor_set(v___x_1464_, 3, v___x_1463_);
lean_ctor_set(v___x_1464_, 4, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1465_, lean_object* v___x_1466_, lean_object* v_declName_1467_, lean_object* v_stx_1468_, uint8_t v_kind_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1468_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1473_) == 0)
{
uint8_t v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; size_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec_ref(v___x_1473_);
v___x_1474_ = 0;
v___x_1475_ = 1;
v___x_1476_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1477_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1478_ = lean_unsigned_to_nat(32u);
v___x_1479_ = lean_mk_empty_array_with_capacity(v___x_1478_);
v___x_1480_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1481_ = ((size_t)5ULL);
lean_inc_n(v___x_1465_, 6);
v___x_1482_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1479_);
lean_ctor_set(v___x_1482_, 2, v___x_1465_);
lean_ctor_set(v___x_1482_, 3, v___x_1465_);
lean_ctor_set_usize(v___x_1482_, 4, v___x_1481_);
v___x_1483_ = lean_box(1);
lean_inc_ref(v___x_1482_);
v___x_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1477_);
lean_ctor_set(v___x_1484_, 1, v___x_1482_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
v___x_1485_ = lean_mk_empty_array_with_capacity(v___x_1465_);
v___x_1486_ = lean_box(0);
lean_inc(v___x_1466_);
v___x_1487_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1487_, 0, v___x_1476_);
lean_ctor_set(v___x_1487_, 1, v___x_1466_);
lean_ctor_set(v___x_1487_, 2, v___x_1484_);
lean_ctor_set(v___x_1487_, 3, v___x_1485_);
lean_ctor_set(v___x_1487_, 4, v___x_1486_);
lean_ctor_set(v___x_1487_, 5, v___x_1465_);
lean_ctor_set(v___x_1487_, 6, v___x_1486_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*7, v___x_1474_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*7 + 1, v___x_1474_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*7 + 2, v___x_1474_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*7 + 3, v___x_1475_);
v___x_1488_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1465_);
lean_ctor_set(v___x_1488_, 1, v___x_1465_);
lean_ctor_set(v___x_1488_, 2, v___x_1465_);
lean_ctor_set(v___x_1488_, 3, v___x_1465_);
lean_ctor_set(v___x_1488_, 4, v___x_1477_);
lean_ctor_set(v___x_1488_, 5, v___x_1477_);
lean_ctor_set(v___x_1488_, 6, v___x_1477_);
lean_ctor_set(v___x_1488_, 7, v___x_1477_);
lean_ctor_set(v___x_1488_, 8, v___x_1477_);
lean_ctor_set(v___x_1488_, 9, v___x_1477_);
v___x_1489_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1490_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1488_);
lean_ctor_set(v___x_1491_, 1, v___x_1489_);
lean_ctor_set(v___x_1491_, 2, v___x_1466_);
lean_ctor_set(v___x_1491_, 3, v___x_1482_);
lean_ctor_set(v___x_1491_, 4, v___x_1490_);
v___x_1492_ = lean_st_mk_ref(v___x_1491_);
v___x_1493_ = l_Lean_Meta_addUnificationHint(v_declName_1467_, v_kind_1469_, v___x_1487_, v___x_1492_, v___y_1470_, v___y_1471_);
lean_dec_ref(v___x_1487_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v___x_1493_, 0);
lean_dec(v_unused_1503_);
v___x_1495_ = v___x_1493_;
v_isShared_1496_ = v_isSharedCheck_1502_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v___x_1493_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1502_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1497_ = lean_st_ref_get(v___x_1492_);
lean_dec(v___x_1492_);
lean_dec(v___x_1497_);
v___x_1498_ = lean_box(0);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1498_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_dec(v___x_1492_);
return v___x_1493_;
}
}
else
{
lean_dec(v_declName_1467_);
lean_dec(v___x_1466_);
lean_dec(v___x_1465_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1504_, lean_object* v___x_1505_, lean_object* v_declName_1506_, lean_object* v_stx_1507_, lean_object* v_kind_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v_kind_boxed_1512_; lean_object* v_res_1513_; 
v_kind_boxed_1512_ = lean_unbox(v_kind_1508_);
v_res_1513_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1504_, v___x_1505_, v_declName_1506_, v_stx_1507_, v_kind_boxed_1512_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v_env_1519_; lean_object* v_options_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1518_ = lean_st_ref_get(v___y_1516_);
v_env_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc_ref(v_env_1519_);
lean_dec(v___x_1518_);
v_options_1520_ = lean_ctor_get(v___y_1515_, 2);
v___x_1521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1522_ = lean_unsigned_to_nat(32u);
v___x_1523_ = lean_mk_empty_array_with_capacity(v___x_1522_);
lean_dec_ref(v___x_1523_);
v___x_1524_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_1520_);
v___x_1525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1525_, 0, v_env_1519_);
lean_ctor_set(v___x_1525_, 1, v___x_1521_);
lean_ctor_set(v___x_1525_, 2, v___x_1524_);
lean_ctor_set(v___x_1525_, 3, v_options_1520_);
v___x_1526_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v_msgData_1514_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_ref_1537_; lean_object* v___x_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1547_; 
v_ref_1537_ = lean_ctor_get(v___y_1534_, 5);
v___x_1538_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msg_1533_, v___y_1534_, v___y_1535_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
lean_inc(v_ref_1537_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_ref_1537_);
lean_ctor_set(v___x_1543_, 1, v_a_1539_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 1);
lean_ctor_set(v___x_1541_, 0, v___x_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1552_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1559_, lean_object* v_decl_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1564_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1565_ = l_Lean_MessageData_ofName(v___x_1559_);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v___x_1568_, v___y_1561_, v___y_1562_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1570_, lean_object* v_decl_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1570_, v_decl_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v_decl_1571_);
return v_res_1575_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = lean_unsigned_to_nat(3033092106u);
v___x_1620_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1621_ = l_Lean_Name_num___override(v___x_1620_, v___x_1619_);
return v___x_1621_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1624_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1625_ = l_Lean_Name_str___override(v___x_1624_, v___x_1623_);
return v___x_1625_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1628_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1629_ = l_Lean_Name_str___override(v___x_1628_, v___x_1627_);
return v___x_1629_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = lean_unsigned_to_nat(2u);
v___x_1631_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1632_ = l_Lean_Name_num___override(v___x_1631_, v___x_1630_);
return v___x_1632_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1639_ = 0;
v___x_1640_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1641_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1642_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1643_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v___x_1641_);
lean_ctor_set(v___x_1643_, 2, v___x_1640_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*3, v___x_1639_);
return v___x_1643_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___f_1644_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___f_1645_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1646_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
lean_ctor_set(v___x_1647_, 1, v___f_1645_);
lean_ctor_set(v___x_1647_, 2, v___f_1644_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1650_ = l_Lean_registerBuiltinAttribute(v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1653_, lean_object* v_msg_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1654_, v___y_1655_, v___y_1656_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1659_, lean_object* v_msg_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(v_00_u03b1_1659_, v_msg_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1664_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0(void){
_start:
{
uint8_t v___x_1665_; uint64_t v___x_1666_; 
v___x_1665_ = 2;
v___x_1666_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* v_p_1667_, lean_object* v_e_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1674_; uint8_t v_foApprox_1675_; uint8_t v_ctxApprox_1676_; uint8_t v_quasiPatternApprox_1677_; uint8_t v_constApprox_1678_; uint8_t v_isDefEqStuckEx_1679_; uint8_t v_unificationHints_1680_; uint8_t v_proofIrrelevance_1681_; uint8_t v_assignSyntheticOpaque_1682_; uint8_t v_offsetCnstrs_1683_; uint8_t v_etaStruct_1684_; uint8_t v_univApprox_1685_; uint8_t v_iota_1686_; uint8_t v_beta_1687_; uint8_t v_proj_1688_; uint8_t v_zeta_1689_; uint8_t v_zetaDelta_1690_; uint8_t v_zetaUnused_1691_; uint8_t v_zetaHave_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1719_; 
v___x_1674_ = l_Lean_Meta_Context_config(v_a_1669_);
v_foApprox_1675_ = lean_ctor_get_uint8(v___x_1674_, 0);
v_ctxApprox_1676_ = lean_ctor_get_uint8(v___x_1674_, 1);
v_quasiPatternApprox_1677_ = lean_ctor_get_uint8(v___x_1674_, 2);
v_constApprox_1678_ = lean_ctor_get_uint8(v___x_1674_, 3);
v_isDefEqStuckEx_1679_ = lean_ctor_get_uint8(v___x_1674_, 4);
v_unificationHints_1680_ = lean_ctor_get_uint8(v___x_1674_, 5);
v_proofIrrelevance_1681_ = lean_ctor_get_uint8(v___x_1674_, 6);
v_assignSyntheticOpaque_1682_ = lean_ctor_get_uint8(v___x_1674_, 7);
v_offsetCnstrs_1683_ = lean_ctor_get_uint8(v___x_1674_, 8);
v_etaStruct_1684_ = lean_ctor_get_uint8(v___x_1674_, 10);
v_univApprox_1685_ = lean_ctor_get_uint8(v___x_1674_, 11);
v_iota_1686_ = lean_ctor_get_uint8(v___x_1674_, 12);
v_beta_1687_ = lean_ctor_get_uint8(v___x_1674_, 13);
v_proj_1688_ = lean_ctor_get_uint8(v___x_1674_, 14);
v_zeta_1689_ = lean_ctor_get_uint8(v___x_1674_, 15);
v_zetaDelta_1690_ = lean_ctor_get_uint8(v___x_1674_, 16);
v_zetaUnused_1691_ = lean_ctor_get_uint8(v___x_1674_, 17);
v_zetaHave_1692_ = lean_ctor_get_uint8(v___x_1674_, 18);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1694_ = v___x_1674_;
v_isShared_1695_ = v_isSharedCheck_1719_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v___x_1674_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1719_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
uint8_t v_trackZetaDelta_1696_; lean_object* v_zetaDeltaSet_1697_; lean_object* v_lctx_1698_; lean_object* v_localInstances_1699_; lean_object* v_defEqCtx_x3f_1700_; lean_object* v_synthPendingDepth_1701_; lean_object* v_canUnfold_x3f_1702_; uint8_t v_univApprox_1703_; uint8_t v_inTypeClassResolution_1704_; uint8_t v_cacheInferType_1705_; uint8_t v___x_1706_; lean_object* v_config_1708_; 
v_trackZetaDelta_1696_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*7);
v_zetaDeltaSet_1697_ = lean_ctor_get(v_a_1669_, 1);
v_lctx_1698_ = lean_ctor_get(v_a_1669_, 2);
v_localInstances_1699_ = lean_ctor_get(v_a_1669_, 3);
v_defEqCtx_x3f_1700_ = lean_ctor_get(v_a_1669_, 4);
v_synthPendingDepth_1701_ = lean_ctor_get(v_a_1669_, 5);
v_canUnfold_x3f_1702_ = lean_ctor_get(v_a_1669_, 6);
v_univApprox_1703_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1704_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*7 + 2);
v_cacheInferType_1705_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*7 + 3);
v___x_1706_ = 2;
if (v_isShared_1695_ == 0)
{
v_config_1708_ = v___x_1694_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 0, v_foApprox_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 1, v_ctxApprox_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 2, v_quasiPatternApprox_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 3, v_constApprox_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 4, v_isDefEqStuckEx_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 5, v_unificationHints_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 6, v_proofIrrelevance_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 7, v_assignSyntheticOpaque_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 8, v_offsetCnstrs_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 10, v_etaStruct_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 11, v_univApprox_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 12, v_iota_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 13, v_beta_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 14, v_proj_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 15, v_zeta_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 16, v_zetaDelta_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 17, v_zetaUnused_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, 18, v_zetaHave_1692_);
v_config_1708_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
uint64_t v___x_1709_; uint64_t v___x_1710_; uint64_t v___x_1711_; uint64_t v___x_1712_; uint64_t v___x_1713_; uint64_t v_key_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_ctor_set_uint8(v_config_1708_, 9, v___x_1706_);
v___x_1709_ = l_Lean_Meta_Context_configKey(v_a_1669_);
v___x_1710_ = 2ULL;
v___x_1711_ = lean_uint64_shift_right(v___x_1709_, v___x_1710_);
v___x_1712_ = lean_uint64_shift_left(v___x_1711_, v___x_1710_);
v___x_1713_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0);
v_key_1714_ = lean_uint64_lor(v___x_1712_, v___x_1713_);
v___x_1715_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1715_, 0, v_config_1708_);
lean_ctor_set_uint64(v___x_1715_, sizeof(void*)*1, v_key_1714_);
lean_inc(v_canUnfold_x3f_1702_);
lean_inc(v_synthPendingDepth_1701_);
lean_inc(v_defEqCtx_x3f_1700_);
lean_inc_ref(v_localInstances_1699_);
lean_inc_ref(v_lctx_1698_);
lean_inc(v_zetaDeltaSet_1697_);
v___x_1716_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v_zetaDeltaSet_1697_);
lean_ctor_set(v___x_1716_, 2, v_lctx_1698_);
lean_ctor_set(v___x_1716_, 3, v_localInstances_1699_);
lean_ctor_set(v___x_1716_, 4, v_defEqCtx_x3f_1700_);
lean_ctor_set(v___x_1716_, 5, v_synthPendingDepth_1701_);
lean_ctor_set(v___x_1716_, 6, v_canUnfold_x3f_1702_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*7, v_trackZetaDelta_1696_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*7 + 1, v_univApprox_1703_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1704_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*7 + 3, v_cacheInferType_1705_);
lean_inc(v_a_1672_);
lean_inc_ref(v_a_1671_);
lean_inc(v_a_1670_);
v___x_1717_ = lean_is_expr_def_eq(v_p_1667_, v_e_1668_, v___x_1716_, v_a_1670_, v_a_1671_, v_a_1672_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object* v_p_1720_, lean_object* v_e_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_p_1720_, v_e_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object* v_x_1728_, lean_object* v_x_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
if (lean_obj_tag(v_x_1728_) == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = l_List_reverse___redArg(v_x_1729_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
else
{
lean_object* v_tail_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1755_; 
v_tail_1737_ = lean_ctor_get(v_x_1728_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_x_1728_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_x_1728_, 0);
lean_dec(v_unused_1756_);
v___x_1739_ = v_x_1728_;
v_isShared_1740_ = v_isSharedCheck_1755_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_tail_1737_);
lean_dec(v_x_1728_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1755_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref(v___x_1741_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v_x_1729_);
lean_ctor_set(v___x_1739_, 0, v_a_1742_);
v___x_1744_ = v___x_1739_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1742_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_x_1729_);
v___x_1744_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v_x_1728_ = v_tail_1737_;
v_x_1729_ = v___x_1744_;
goto _start;
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_del_object(v___x_1739_);
lean_dec(v_tail_1737_);
lean_dec(v_x_1729_);
v_a_1747_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1741_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1741_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v_x_1757_, v_x_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v_res_1764_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1765_; double v___x_1766_; 
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_float_of_nat(v___x_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object* v_cls_1770_, lean_object* v_msg_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_ref_1777_; lean_object* v___x_1778_; lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1823_; 
v_ref_1777_ = lean_ctor_get(v___y_1774_, 5);
v___x_1778_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1823_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1823_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v_traceState_1784_; lean_object* v_env_1785_; lean_object* v_nextMacroScope_1786_; lean_object* v_ngen_1787_; lean_object* v_auxDeclNGen_1788_; lean_object* v_cache_1789_; lean_object* v_messages_1790_; lean_object* v_infoState_1791_; lean_object* v_snapshotTasks_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1822_; 
v___x_1783_ = lean_st_ref_take(v___y_1775_);
v_traceState_1784_ = lean_ctor_get(v___x_1783_, 4);
v_env_1785_ = lean_ctor_get(v___x_1783_, 0);
v_nextMacroScope_1786_ = lean_ctor_get(v___x_1783_, 1);
v_ngen_1787_ = lean_ctor_get(v___x_1783_, 2);
v_auxDeclNGen_1788_ = lean_ctor_get(v___x_1783_, 3);
v_cache_1789_ = lean_ctor_get(v___x_1783_, 5);
v_messages_1790_ = lean_ctor_get(v___x_1783_, 6);
v_infoState_1791_ = lean_ctor_get(v___x_1783_, 7);
v_snapshotTasks_1792_ = lean_ctor_get(v___x_1783_, 8);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1794_ = v___x_1783_;
v_isShared_1795_ = v_isSharedCheck_1822_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_snapshotTasks_1792_);
lean_inc(v_infoState_1791_);
lean_inc(v_messages_1790_);
lean_inc(v_cache_1789_);
lean_inc(v_traceState_1784_);
lean_inc(v_auxDeclNGen_1788_);
lean_inc(v_ngen_1787_);
lean_inc(v_nextMacroScope_1786_);
lean_inc(v_env_1785_);
lean_dec(v___x_1783_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1822_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
uint64_t v_tid_1796_; lean_object* v_traces_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1821_; 
v_tid_1796_ = lean_ctor_get_uint64(v_traceState_1784_, sizeof(void*)*1);
v_traces_1797_ = lean_ctor_get(v_traceState_1784_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_traceState_1784_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1799_ = v_traceState_1784_;
v_isShared_1800_ = v_isSharedCheck_1821_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_traces_1797_);
lean_dec(v_traceState_1784_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1821_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; double v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
v___x_1803_ = 0;
v___x_1804_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_1805_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1805_, 0, v_cls_1770_);
lean_ctor_set(v___x_1805_, 1, v___x_1801_);
lean_ctor_set(v___x_1805_, 2, v___x_1804_);
lean_ctor_set_float(v___x_1805_, sizeof(void*)*3, v___x_1802_);
lean_ctor_set_float(v___x_1805_, sizeof(void*)*3 + 8, v___x_1802_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*3 + 16, v___x_1803_);
v___x_1806_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2));
v___x_1807_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v_a_1779_);
lean_ctor_set(v___x_1807_, 2, v___x_1806_);
lean_inc(v_ref_1777_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_ref_1777_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Lean_PersistentArray_push___redArg(v_traces_1797_, v___x_1808_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1809_);
v___x_1811_ = v___x_1799_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1809_);
lean_ctor_set_uint64(v_reuseFailAlloc_1820_, sizeof(void*)*1, v_tid_1796_);
v___x_1811_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 4, v___x_1811_);
v___x_1813_ = v___x_1794_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_env_1785_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_nextMacroScope_1786_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_ngen_1787_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_auxDeclNGen_1788_);
lean_ctor_set(v_reuseFailAlloc_1819_, 4, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1819_, 5, v_cache_1789_);
lean_ctor_set(v_reuseFailAlloc_1819_, 6, v_messages_1790_);
lean_ctor_set(v_reuseFailAlloc_1819_, 7, v_infoState_1791_);
lean_ctor_set(v_reuseFailAlloc_1819_, 8, v_snapshotTasks_1792_);
v___x_1813_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1814_ = lean_st_ref_set(v___y_1775_, v___x_1813_);
v___x_1815_ = lean_box(0);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1815_);
v___x_1817_ = v___x_1781_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object* v_cls_1824_, lean_object* v_msg_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_1824_, v_msg_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object* v_as_1835_, size_t v_sz_1836_, size_t v_i_1837_, lean_object* v_b_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_a_1845_; uint8_t v___x_1849_; 
v___x_1849_ = lean_usize_dec_lt(v_i_1837_, v_sz_1836_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_b_1838_);
return v___x_1850_;
}
else
{
lean_object* v_snd_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1941_; 
v_snd_1851_ = lean_ctor_get(v_b_1838_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_b_1838_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v_b_1838_, 0);
lean_dec(v_unused_1942_);
v___x_1853_ = v_b_1838_;
v_isShared_1854_ = v_isSharedCheck_1941_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_snd_1851_);
lean_dec(v_b_1838_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1941_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_array_1855_; lean_object* v_start_1856_; lean_object* v_stop_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v_array_1855_ = lean_ctor_get(v_snd_1851_, 0);
v_start_1856_ = lean_ctor_get(v_snd_1851_, 1);
v_stop_1857_ = lean_ctor_get(v_snd_1851_, 2);
v___x_1858_ = lean_box(0);
v___x_1859_ = lean_nat_dec_lt(v_start_1856_, v_stop_1857_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1861_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1858_);
v___x_1861_ = v___x_1853_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_snd_1851_);
v___x_1861_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
}
else
{
lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1937_; 
lean_inc(v_stop_1857_);
lean_inc(v_start_1856_);
lean_inc_ref(v_array_1855_);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_snd_1851_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; lean_object* v_unused_1939_; lean_object* v_unused_1940_; 
v_unused_1938_ = lean_ctor_get(v_snd_1851_, 2);
lean_dec(v_unused_1938_);
v_unused_1939_ = lean_ctor_get(v_snd_1851_, 1);
lean_dec(v_unused_1939_);
v_unused_1940_ = lean_ctor_get(v_snd_1851_, 0);
lean_dec(v_unused_1940_);
v___x_1865_ = v_snd_1851_;
v_isShared_1866_ = v_isSharedCheck_1937_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v_snd_1851_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1937_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1867_ = lean_array_fget(v_array_1855_, v_start_1856_);
v___x_1868_ = lean_unsigned_to_nat(1u);
v___x_1869_ = lean_nat_add(v_start_1856_, v___x_1868_);
lean_dec(v_start_1856_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v___x_1869_);
v___x_1871_ = v___x_1865_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_array_1855_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_stop_1857_);
v___x_1871_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
uint8_t v___x_1872_; uint8_t v___x_1873_; uint8_t v___x_1874_; 
v___x_1872_ = 3;
v___x_1873_ = lean_unbox(v___x_1867_);
lean_dec(v___x_1867_);
v___x_1874_ = l_Lean_instBEqBinderInfo_beq(v___x_1873_, v___x_1872_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1876_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1871_);
lean_ctor_set(v___x_1853_, 0, v___x_1858_);
v___x_1876_ = v___x_1853_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
v_a_1845_ = v___x_1876_;
goto v___jp_1844_;
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1879_; 
v_a_1878_ = lean_array_uget_borrowed(v_as_1835_, v_i_1837_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v_a_1878_);
v___x_1879_ = lean_infer_type(v_a_1878_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1881_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref(v___x_1879_);
v___x_1881_ = l_Lean_Meta_trySynthInstance(v_a_1880_, v___x_1858_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1919_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1919_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1919_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
if (lean_obj_tag(v_a_1882_) == 1)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
lean_del_object(v___x_1884_);
v_a_1886_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v_a_1882_);
lean_inc(v_a_1878_);
v___x_1887_ = l_Lean_Meta_isExprDefEq(v_a_1878_, v_a_1886_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1903_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1903_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1903_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
uint8_t v___x_1892_; 
v___x_1892_ = lean_unbox(v_a_1888_);
lean_dec(v_a_1888_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1871_);
lean_ctor_set(v___x_1853_, 0, v___x_1893_);
v___x_1895_ = v___x_1853_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1871_);
v___x_1895_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1895_);
v___x_1897_ = v___x_1890_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_object* v___x_1901_; 
lean_del_object(v___x_1890_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1871_);
lean_ctor_set(v___x_1853_, 0, v___x_1858_);
v___x_1901_ = v___x_1853_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v___x_1871_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v_a_1845_ = v___x_1901_;
goto v___jp_1844_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref(v___x_1871_);
lean_del_object(v___x_1853_);
v_a_1904_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1887_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1887_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
lean_dec(v_a_1882_);
v___x_1912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1871_);
lean_ctor_set(v___x_1853_, 0, v___x_1912_);
v___x_1914_ = v___x_1853_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1871_);
v___x_1914_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1914_);
v___x_1916_ = v___x_1884_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v___x_1871_);
lean_del_object(v___x_1853_);
v_a_1920_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1881_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1881_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v___x_1871_);
lean_del_object(v___x_1853_);
v_a_1928_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1879_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1879_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
}
}
}
v___jp_1844_:
{
size_t v___x_1846_; size_t v___x_1847_; 
v___x_1846_ = ((size_t)1ULL);
v___x_1847_ = lean_usize_add(v_i_1837_, v___x_1846_);
v_i_1837_ = v___x_1847_;
v_b_1838_ = v_a_1845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object* v_as_1943_, lean_object* v_sz_1944_, lean_object* v_i_1945_, lean_object* v_b_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
size_t v_sz_boxed_1952_; size_t v_i_boxed_1953_; lean_object* v_res_1954_; 
v_sz_boxed_1952_ = lean_unbox_usize(v_sz_1944_);
lean_dec(v_sz_1944_);
v_i_boxed_1953_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_res_1954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_as_1943_, v_sz_boxed_1952_, v_i_boxed_1953_, v_b_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec_ref(v_as_1943_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object* v_as_x27_1958_, lean_object* v_b_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
if (lean_obj_tag(v_as_x27_1958_) == 0)
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_b_1959_);
return v___x_1965_;
}
else
{
lean_object* v_head_1966_; lean_object* v_tail_1967_; lean_object* v_lhs_1968_; lean_object* v_rhs_1969_; lean_object* v___x_1970_; 
lean_dec_ref(v_b_1959_);
v_head_1966_ = lean_ctor_get(v_as_x27_1958_, 0);
v_tail_1967_ = lean_ctor_get(v_as_x27_1958_, 1);
v_lhs_1968_ = lean_ctor_get(v_head_1966_, 0);
v_rhs_1969_ = lean_ctor_get(v_head_1966_, 1);
lean_inc(v___y_1963_);
lean_inc_ref(v___y_1962_);
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc_ref(v_rhs_1969_);
lean_inc_ref(v_lhs_1968_);
v___x_1970_ = lean_is_expr_def_eq(v_lhs_1968_, v_rhs_1969_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1984_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1984_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1984_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1975_ = lean_box(0);
v___x_1976_ = lean_unbox(v_a_1971_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_a_1971_);
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v___x_1975_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1978_);
v___x_1980_ = v___x_1973_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
else
{
lean_object* v___x_1982_; 
lean_del_object(v___x_1973_);
lean_dec(v_a_1971_);
v___x_1982_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_as_x27_1958_ = v_tail_1967_;
v_b_1959_ = v___x_1982_;
goto _start;
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
v_a_1985_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1970_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1970_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object* v_as_x27_1993_, lean_object* v_b_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_1993_, v_b_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v_as_x27_1993_);
return v_res_2000_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2001_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8(void){
_start:
{
lean_object* v_cls_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_cls_2016_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2017_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7));
v___x_2018_ = l_Lean_Name_append(v___x_2017_, v_cls_2016_);
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object* v_candidate_2022_, lean_object* v_t_2023_, lean_object* v_s_2024_, uint8_t v_mayPostpone_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_Meta_saveState___redArg(v_a_2027_, v_a_2029_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2282_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2282_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2282_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___y_2037_; uint8_t v___y_2038_; lean_object* v_a_2060_; uint8_t v_a_2064_; lean_object* v___x_2076_; lean_object* v_cache_2077_; lean_object* v_mctx_2078_; lean_object* v_zetaDeltaFVarIds_2079_; lean_object* v_postponed_2080_; lean_object* v_diag_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2281_; 
v___x_2076_ = lean_st_ref_take(v_a_2027_);
v_cache_2077_ = lean_ctor_get(v___x_2076_, 1);
v_mctx_2078_ = lean_ctor_get(v___x_2076_, 0);
v_zetaDeltaFVarIds_2079_ = lean_ctor_get(v___x_2076_, 2);
v_postponed_2080_ = lean_ctor_get(v___x_2076_, 3);
v_diag_2081_ = lean_ctor_get(v___x_2076_, 4);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2083_ = v___x_2076_;
v_isShared_2084_ = v_isSharedCheck_2281_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_diag_2081_);
lean_inc(v_postponed_2080_);
lean_inc(v_zetaDeltaFVarIds_2079_);
lean_inc(v_cache_2077_);
lean_inc(v_mctx_2078_);
lean_dec(v___x_2076_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2281_;
goto v_resetjp_2082_;
}
v___jp_2036_:
{
if (v___y_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_del_object(v___x_2034_);
v___x_2039_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2032_, v_a_2027_, v_a_2029_);
lean_dec(v_a_2032_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v___x_2039_, 0);
lean_dec(v_unused_2047_);
v___x_2041_ = v___x_2039_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_dec(v___x_2039_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 1);
lean_ctor_set(v___x_2041_, 0, v___y_2037_);
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___y_2037_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v___y_2037_);
v_a_2048_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2039_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2039_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v___x_2057_; 
lean_dec(v_a_2032_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 1);
lean_ctor_set(v___x_2034_, 0, v___y_2037_);
v___x_2057_ = v___x_2034_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___y_2037_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
v___jp_2059_:
{
uint8_t v___x_2061_; 
v___x_2061_ = l_Lean_Exception_isInterrupt(v_a_2060_);
if (v___x_2061_ == 0)
{
uint8_t v___x_2062_; 
lean_inc_ref(v_a_2060_);
v___x_2062_ = l_Lean_Exception_isRuntime(v_a_2060_);
v___y_2037_ = v_a_2060_;
v___y_2038_ = v___x_2062_;
goto v___jp_2036_;
}
else
{
v___y_2037_ = v_a_2060_;
v___y_2038_ = v___x_2061_;
goto v___jp_2036_;
}
}
v___jp_2063_:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2032_, v_a_2027_, v_a_2029_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_2034_);
lean_dec(v_a_2032_);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2074_);
v___x_2067_ = v___x_2065_;
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v___x_2065_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = lean_box(v_a_2064_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2069_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2075_; 
v_a_2075_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2065_);
v_a_2060_ = v_a_2075_;
goto v___jp_2059_;
}
}
v_resetjp_2082_:
{
lean_object* v_inferType_2085_; lean_object* v_funInfo_2086_; lean_object* v_synthInstance_2087_; lean_object* v_whnf_2088_; lean_object* v_defEqPerm_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2279_; 
v_inferType_2085_ = lean_ctor_get(v_cache_2077_, 0);
v_funInfo_2086_ = lean_ctor_get(v_cache_2077_, 1);
v_synthInstance_2087_ = lean_ctor_get(v_cache_2077_, 2);
v_whnf_2088_ = lean_ctor_get(v_cache_2077_, 3);
v_defEqPerm_2089_ = lean_ctor_get(v_cache_2077_, 5);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_cache_2077_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; 
v_unused_2280_ = lean_ctor_get(v_cache_2077_, 4);
lean_dec(v_unused_2280_);
v___x_2091_ = v_cache_2077_;
v_isShared_2092_ = v_isSharedCheck_2279_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_defEqPerm_2089_);
lean_inc(v_whnf_2088_);
lean_inc(v_synthInstance_2087_);
lean_inc(v_funInfo_2086_);
lean_inc(v_inferType_2085_);
lean_dec(v_cache_2077_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2279_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 4, v___x_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_inferType_2085_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_funInfo_2086_);
lean_ctor_set(v_reuseFailAlloc_2278_, 2, v_synthInstance_2087_);
lean_ctor_set(v_reuseFailAlloc_2278_, 3, v_whnf_2088_);
lean_ctor_set(v_reuseFailAlloc_2278_, 4, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2278_, 5, v_defEqPerm_2089_);
v___x_2095_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2095_);
v___x_2097_ = v___x_2083_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_mctx_2078_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_zetaDeltaFVarIds_2079_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v_postponed_2080_);
lean_ctor_set(v_reuseFailAlloc_2277_, 4, v_diag_2081_);
v___x_2097_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_st_ref_set(v_a_2027_, v___x_2097_);
v___x_2099_ = l_Lean_Meta_getResetPostponed___redArg(v_a_2027_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; uint8_t v_a_2102_; lean_object* v___x_2143_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v___x_2099_);
lean_inc(v_candidate_2022_);
v___x_2143_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_candidate_2022_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref(v___x_2143_);
v___x_2145_ = l_Lean_ConstantInfo_levelParams(v_a_2144_);
v___x_2146_ = lean_box(0);
v___x_2147_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v___x_2145_, v___x_2146_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = 0;
v___x_2150_ = l_Lean_Core_instantiateValueLevelParams(v_a_2144_, v_a_2148_, v___x_2149_, v_a_2028_, v_a_2029_);
lean_dec(v_a_2144_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v___x_2150_);
v___x_2152_ = lean_box(0);
v___x_2153_ = l_Lean_Meta_lambdaMetaTelescope(v_a_2151_, v___x_2152_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
lean_dec(v_a_2151_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v_snd_2155_; lean_object* v_fst_2156_; lean_object* v_fst_2157_; lean_object* v_snd_2158_; lean_object* v___x_2159_; uint8_t v_foApprox_2160_; uint8_t v_ctxApprox_2161_; uint8_t v_quasiPatternApprox_2162_; uint8_t v_constApprox_2163_; uint8_t v_isDefEqStuckEx_2164_; uint8_t v_proofIrrelevance_2165_; uint8_t v_assignSyntheticOpaque_2166_; uint8_t v_offsetCnstrs_2167_; uint8_t v_transparency_2168_; uint8_t v_etaStruct_2169_; uint8_t v_univApprox_2170_; uint8_t v_iota_2171_; uint8_t v_beta_2172_; uint8_t v_proj_2173_; uint8_t v_zeta_2174_; uint8_t v_zetaDelta_2175_; uint8_t v_zetaUnused_2176_; uint8_t v_zetaHave_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2264_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2153_);
v_snd_2155_ = lean_ctor_get(v_a_2154_, 1);
lean_inc(v_snd_2155_);
v_fst_2156_ = lean_ctor_get(v_a_2154_, 0);
lean_inc(v_fst_2156_);
lean_dec(v_a_2154_);
v_fst_2157_ = lean_ctor_get(v_snd_2155_, 0);
lean_inc(v_fst_2157_);
v_snd_2158_ = lean_ctor_get(v_snd_2155_, 1);
lean_inc(v_snd_2158_);
lean_dec(v_snd_2155_);
v___x_2159_ = l_Lean_Meta_Context_config(v_a_2026_);
v_foApprox_2160_ = lean_ctor_get_uint8(v___x_2159_, 0);
v_ctxApprox_2161_ = lean_ctor_get_uint8(v___x_2159_, 1);
v_quasiPatternApprox_2162_ = lean_ctor_get_uint8(v___x_2159_, 2);
v_constApprox_2163_ = lean_ctor_get_uint8(v___x_2159_, 3);
v_isDefEqStuckEx_2164_ = lean_ctor_get_uint8(v___x_2159_, 4);
v_proofIrrelevance_2165_ = lean_ctor_get_uint8(v___x_2159_, 6);
v_assignSyntheticOpaque_2166_ = lean_ctor_get_uint8(v___x_2159_, 7);
v_offsetCnstrs_2167_ = lean_ctor_get_uint8(v___x_2159_, 8);
v_transparency_2168_ = lean_ctor_get_uint8(v___x_2159_, 9);
v_etaStruct_2169_ = lean_ctor_get_uint8(v___x_2159_, 10);
v_univApprox_2170_ = lean_ctor_get_uint8(v___x_2159_, 11);
v_iota_2171_ = lean_ctor_get_uint8(v___x_2159_, 12);
v_beta_2172_ = lean_ctor_get_uint8(v___x_2159_, 13);
v_proj_2173_ = lean_ctor_get_uint8(v___x_2159_, 14);
v_zeta_2174_ = lean_ctor_get_uint8(v___x_2159_, 15);
v_zetaDelta_2175_ = lean_ctor_get_uint8(v___x_2159_, 16);
v_zetaUnused_2176_ = lean_ctor_get_uint8(v___x_2159_, 17);
v_zetaHave_2177_ = lean_ctor_get_uint8(v___x_2159_, 18);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2179_ = v___x_2159_;
v_isShared_2180_ = v_isSharedCheck_2264_;
goto v_resetjp_2178_;
}
else
{
lean_dec(v___x_2159_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2264_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; 
v___x_2181_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_2158_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_dec_ref(v___x_2181_);
lean_del_object(v___x_2179_);
lean_dec(v_fst_2157_);
lean_dec(v_fst_2156_);
lean_dec(v_a_2100_);
lean_dec_ref(v_s_2024_);
lean_dec_ref(v_t_2023_);
lean_dec(v_candidate_2022_);
v_a_2064_ = v___x_2149_;
goto v___jp_2063_;
}
else
{
lean_object* v_a_2182_; uint8_t v_trackZetaDelta_2183_; lean_object* v_zetaDeltaSet_2184_; lean_object* v_lctx_2185_; lean_object* v_localInstances_2186_; lean_object* v_defEqCtx_x3f_2187_; lean_object* v_synthPendingDepth_2188_; lean_object* v_canUnfold_x3f_2189_; uint8_t v_univApprox_2190_; uint8_t v_inTypeClassResolution_2191_; uint8_t v_cacheInferType_2192_; lean_object* v_pattern_2193_; lean_object* v_constraints_2194_; uint8_t v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v_lhs_2227_; lean_object* v_rhs_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2263_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
v_trackZetaDelta_2183_ = lean_ctor_get_uint8(v_a_2026_, sizeof(void*)*7);
v_zetaDeltaSet_2184_ = lean_ctor_get(v_a_2026_, 1);
v_lctx_2185_ = lean_ctor_get(v_a_2026_, 2);
v_localInstances_2186_ = lean_ctor_get(v_a_2026_, 3);
v_defEqCtx_x3f_2187_ = lean_ctor_get(v_a_2026_, 4);
v_synthPendingDepth_2188_ = lean_ctor_get(v_a_2026_, 5);
v_canUnfold_x3f_2189_ = lean_ctor_get(v_a_2026_, 6);
v_univApprox_2190_ = lean_ctor_get_uint8(v_a_2026_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2191_ = lean_ctor_get_uint8(v_a_2026_, sizeof(void*)*7 + 2);
v_cacheInferType_2192_ = lean_ctor_get_uint8(v_a_2026_, sizeof(void*)*7 + 3);
v_pattern_2193_ = lean_ctor_get(v_a_2182_, 0);
lean_inc_ref(v_pattern_2193_);
v_constraints_2194_ = lean_ctor_get(v_a_2182_, 1);
lean_inc(v_constraints_2194_);
lean_dec(v_a_2182_);
v_lhs_2227_ = lean_ctor_get(v_pattern_2193_, 0);
v_rhs_2228_ = lean_ctor_get(v_pattern_2193_, 1);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_pattern_2193_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2230_ = v_pattern_2193_;
v_isShared_2231_ = v_isSharedCheck_2263_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_rhs_2228_);
lean_inc(v_lhs_2227_);
lean_dec(v_pattern_2193_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2263_;
goto v_resetjp_2229_;
}
v___jp_2195_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2202_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_constraints_2194_, v___x_2201_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v_constraints_2194_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v_fst_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2224_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v_fst_2204_ = lean_ctor_get(v_a_2203_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_a_2203_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v_a_2203_, 1);
lean_dec(v_unused_2225_);
v___x_2206_ = v_a_2203_;
v_isShared_2207_ = v_isSharedCheck_2224_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_fst_2204_);
lean_dec(v_a_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2224_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
if (lean_obj_tag(v_fst_2204_) == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2208_ = lean_unsigned_to_nat(0u);
v___x_2209_ = lean_array_get_size(v_fst_2157_);
v___x_2210_ = l_Array_toSubarray___redArg(v_fst_2157_, v___x_2208_, v___x_2209_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 1, v___x_2210_);
lean_ctor_set(v___x_2206_, 0, v___x_2152_);
v___x_2212_ = v___x_2206_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
size_t v_sz_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v_sz_2213_ = lean_array_size(v_fst_2156_);
v___x_2214_ = ((size_t)0ULL);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_fst_2156_, v_sz_2213_, v___x_2214_, v___x_2212_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v_fst_2156_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v_fst_2217_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref(v___x_2215_);
v_fst_2217_ = lean_ctor_get(v_a_2216_, 0);
lean_inc(v_fst_2217_);
lean_dec(v_a_2216_);
if (lean_obj_tag(v_fst_2217_) == 0)
{
v_a_2102_ = v___y_2196_;
goto v___jp_2101_;
}
else
{
lean_object* v_val_2218_; uint8_t v___x_2219_; 
v_val_2218_ = lean_ctor_get(v_fst_2217_, 0);
lean_inc(v_val_2218_);
lean_dec_ref(v_fst_2217_);
v___x_2219_ = lean_unbox(v_val_2218_);
lean_dec(v_val_2218_);
v_a_2102_ = v___x_2219_;
goto v___jp_2101_;
}
}
else
{
lean_object* v_a_2220_; 
lean_dec(v_a_2100_);
v_a_2220_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2220_);
lean_dec_ref(v___x_2215_);
v_a_2060_ = v_a_2220_;
goto v___jp_2059_;
}
}
}
else
{
lean_object* v_val_2222_; uint8_t v___x_2223_; 
lean_del_object(v___x_2206_);
lean_dec(v_fst_2157_);
lean_dec(v_fst_2156_);
v_val_2222_ = lean_ctor_get(v_fst_2204_, 0);
lean_inc(v_val_2222_);
lean_dec_ref(v_fst_2204_);
v___x_2223_ = lean_unbox(v_val_2222_);
lean_dec(v_val_2222_);
v_a_2102_ = v___x_2223_;
goto v___jp_2101_;
}
}
}
else
{
lean_object* v_a_2226_; 
lean_dec(v_fst_2157_);
lean_dec(v_fst_2156_);
lean_dec(v_a_2100_);
v_a_2226_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2226_);
lean_dec_ref(v___x_2202_);
v_a_2060_ = v_a_2226_;
goto v___jp_2059_;
}
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2180_ == 0)
{
v___x_2233_ = v___x_2179_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 0, v_foApprox_2160_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 1, v_ctxApprox_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 2, v_quasiPatternApprox_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 3, v_constApprox_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 4, v_isDefEqStuckEx_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 6, v_proofIrrelevance_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 7, v_assignSyntheticOpaque_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 8, v_offsetCnstrs_2167_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 9, v_transparency_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 10, v_etaStruct_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 11, v_univApprox_2170_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 12, v_iota_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 13, v_beta_2172_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 14, v_proj_2173_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 15, v_zeta_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 16, v_zetaDelta_2175_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 17, v_zetaUnused_2176_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, 18, v_zetaHave_2177_);
v___x_2233_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
uint64_t v___x_2234_; lean_object* v_cls_2235_; lean_object* v___y_2237_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_ctor_set_uint8(v___x_2233_, 5, v___x_2149_);
v___x_2234_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2233_);
v_cls_2235_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2256_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2256_, 0, v___x_2233_);
lean_ctor_set_uint64(v___x_2256_, sizeof(void*)*1, v___x_2234_);
lean_inc(v_canUnfold_x3f_2189_);
lean_inc(v_synthPendingDepth_2188_);
lean_inc(v_defEqCtx_x3f_2187_);
lean_inc_ref(v_localInstances_2186_);
lean_inc_ref(v_lctx_2185_);
lean_inc(v_zetaDeltaSet_2184_);
v___x_2257_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v_zetaDeltaSet_2184_);
lean_ctor_set(v___x_2257_, 2, v_lctx_2185_);
lean_ctor_set(v___x_2257_, 3, v_localInstances_2186_);
lean_ctor_set(v___x_2257_, 4, v_defEqCtx_x3f_2187_);
lean_ctor_set(v___x_2257_, 5, v_synthPendingDepth_2188_);
lean_ctor_set(v___x_2257_, 6, v_canUnfold_x3f_2189_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*7, v_trackZetaDelta_2183_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*7 + 1, v_univApprox_2190_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2191_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*7 + 3, v_cacheInferType_2192_);
v___x_2258_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_lhs_2227_, v_t_2023_, v___x_2257_, v_a_2027_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; uint8_t v___x_2260_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
v___x_2260_ = lean_unbox(v_a_2259_);
lean_dec(v_a_2259_);
if (v___x_2260_ == 0)
{
lean_dec_ref(v___x_2257_);
lean_dec_ref(v_rhs_2228_);
lean_dec_ref(v_s_2024_);
v___y_2237_ = v___x_2258_;
goto v___jp_2236_;
}
else
{
lean_object* v___x_2261_; 
lean_dec_ref(v___x_2258_);
v___x_2261_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_rhs_2228_, v_s_2024_, v___x_2257_, v_a_2027_, v_a_2028_, v_a_2029_);
lean_dec_ref(v___x_2257_);
v___y_2237_ = v___x_2261_;
goto v___jp_2236_;
}
}
else
{
lean_dec_ref(v___x_2257_);
lean_dec_ref(v_rhs_2228_);
lean_dec_ref(v_s_2024_);
v___y_2237_ = v___x_2258_;
goto v___jp_2236_;
}
v___jp_2236_:
{
if (lean_obj_tag(v___y_2237_) == 0)
{
lean_object* v_a_2238_; uint8_t v___x_2239_; 
v_a_2238_ = lean_ctor_get(v___y_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v___y_2237_);
v___x_2239_ = lean_unbox(v_a_2238_);
if (v___x_2239_ == 0)
{
lean_dec(v_a_2238_);
lean_del_object(v___x_2230_);
lean_dec(v_constraints_2194_);
lean_dec(v_fst_2157_);
lean_dec(v_fst_2156_);
lean_dec(v_a_2100_);
lean_dec(v_candidate_2022_);
v_a_2064_ = v___x_2149_;
goto v___jp_2063_;
}
else
{
lean_object* v_options_2240_; uint8_t v_hasTrace_2241_; 
v_options_2240_ = lean_ctor_get(v_a_2028_, 2);
v_hasTrace_2241_ = lean_ctor_get_uint8(v_options_2240_, sizeof(void*)*1);
if (v_hasTrace_2241_ == 0)
{
uint8_t v___x_2242_; 
lean_del_object(v___x_2230_);
lean_dec(v_candidate_2022_);
v___x_2242_ = lean_unbox(v_a_2238_);
lean_dec(v_a_2238_);
v___y_2196_ = v___x_2242_;
v___y_2197_ = v_a_2026_;
v___y_2198_ = v_a_2027_;
v___y_2199_ = v_a_2028_;
v___y_2200_ = v_a_2029_;
goto v___jp_2195_;
}
else
{
lean_object* v_inheritedTraceOptions_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v_inheritedTraceOptions_2243_ = lean_ctor_get(v_a_2028_, 13);
v___x_2244_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2245_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2243_, v_options_2240_, v___x_2244_);
if (v___x_2245_ == 0)
{
uint8_t v___x_2246_; 
lean_del_object(v___x_2230_);
lean_dec(v_candidate_2022_);
v___x_2246_ = lean_unbox(v_a_2238_);
lean_dec(v_a_2238_);
v___y_2196_ = v___x_2246_;
v___y_2197_ = v_a_2026_;
v___y_2198_ = v_a_2027_;
v___y_2199_ = v_a_2028_;
v___y_2200_ = v_a_2029_;
goto v___jp_2195_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2247_ = l_Lean_MessageData_ofName(v_candidate_2022_);
v___x_2248_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10);
if (v_isShared_2231_ == 0)
{
lean_ctor_set_tag(v___x_2230_, 7);
lean_ctor_set(v___x_2230_, 1, v___x_2248_);
lean_ctor_set(v___x_2230_, 0, v___x_2247_);
v___x_2250_ = v___x_2230_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2235_, v___x_2250_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2251_) == 0)
{
uint8_t v___x_2252_; 
lean_dec_ref(v___x_2251_);
v___x_2252_ = lean_unbox(v_a_2238_);
lean_dec(v_a_2238_);
v___y_2196_ = v___x_2252_;
v___y_2197_ = v_a_2026_;
v___y_2198_ = v_a_2027_;
v___y_2199_ = v_a_2028_;
v___y_2200_ = v_a_2029_;
goto v___jp_2195_;
}
else
{
lean_object* v_a_2253_; 
lean_dec(v_a_2238_);
lean_dec(v_constraints_2194_);
lean_dec(v_fst_2157_);
lean_dec(v_fst_2156_);
lean_dec(v_a_2100_);
v_a_2253_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___x_2251_);
v_a_2060_ = v_a_2253_;
goto v___jp_2059_;
}
}
}
}
}
}
else
{
lean_object* v_a_2255_; 
lean_del_object(v___x_2230_);
lean_dec(v_constraints_2194_);
lean_dec(v_fst_2157_);
lean_dec(v_fst_2156_);
lean_dec(v_a_2100_);
lean_dec(v_candidate_2022_);
v_a_2255_ = lean_ctor_get(v___y_2237_, 0);
lean_inc(v_a_2255_);
lean_dec_ref(v___y_2237_);
v_a_2060_ = v_a_2255_;
goto v___jp_2059_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2265_; 
lean_dec(v_a_2100_);
lean_dec_ref(v_s_2024_);
lean_dec_ref(v_t_2023_);
lean_dec(v_candidate_2022_);
v_a_2265_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2265_);
lean_dec_ref(v___x_2153_);
v_a_2060_ = v_a_2265_;
goto v___jp_2059_;
}
}
else
{
lean_object* v_a_2266_; 
lean_dec(v_a_2100_);
lean_dec_ref(v_s_2024_);
lean_dec_ref(v_t_2023_);
lean_dec(v_candidate_2022_);
v_a_2266_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2266_);
lean_dec_ref(v___x_2150_);
v_a_2060_ = v_a_2266_;
goto v___jp_2059_;
}
}
else
{
lean_object* v_a_2267_; 
lean_dec(v_a_2144_);
lean_dec(v_a_2100_);
lean_dec_ref(v_s_2024_);
lean_dec_ref(v_t_2023_);
lean_dec(v_candidate_2022_);
v_a_2267_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2147_);
v_a_2060_ = v_a_2267_;
goto v___jp_2059_;
}
}
else
{
lean_object* v_a_2268_; 
lean_dec(v_a_2100_);
lean_dec_ref(v_s_2024_);
lean_dec_ref(v_t_2023_);
lean_dec(v_candidate_2022_);
v_a_2268_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2268_);
lean_dec_ref(v___x_2143_);
v_a_2060_ = v_a_2268_;
goto v___jp_2059_;
}
v___jp_2101_:
{
if (v_a_2102_ == 0)
{
lean_dec(v_a_2100_);
v_a_2064_ = v_a_2102_;
goto v___jp_2063_;
}
else
{
uint8_t v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = 0;
v___x_2104_ = l_Lean_Meta_processPostponed(v_mayPostpone_2025_, v___x_2103_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2141_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2107_ = v___x_2104_;
v_isShared_2108_ = v_isSharedCheck_2141_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2141_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_unbox(v_a_2105_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_del_object(v___x_2107_);
lean_dec(v_a_2105_);
lean_dec(v_a_2100_);
v___x_2110_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2032_, v_a_2027_, v_a_2029_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
lean_del_object(v___x_2034_);
lean_dec(v_a_2032_);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v___x_2110_, 0);
lean_dec(v_unused_2119_);
v___x_2112_ = v___x_2110_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v___x_2110_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_box(v___x_2103_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
else
{
lean_object* v_a_2120_; 
v_a_2120_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2110_);
v_a_2060_ = v_a_2120_;
goto v___jp_2059_;
}
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v_postponed_2123_; lean_object* v_mctx_2124_; lean_object* v_cache_2125_; lean_object* v_zetaDeltaFVarIds_2126_; lean_object* v_diag_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2139_; 
lean_del_object(v___x_2034_);
lean_dec(v_a_2032_);
v___x_2121_ = lean_st_ref_get(v_a_2027_);
v___x_2122_ = lean_st_ref_take(v_a_2027_);
v_postponed_2123_ = lean_ctor_get(v___x_2121_, 3);
lean_inc_ref(v_postponed_2123_);
lean_dec(v___x_2121_);
v_mctx_2124_ = lean_ctor_get(v___x_2122_, 0);
v_cache_2125_ = lean_ctor_get(v___x_2122_, 1);
v_zetaDeltaFVarIds_2126_ = lean_ctor_get(v___x_2122_, 2);
v_diag_2127_ = lean_ctor_get(v___x_2122_, 4);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; 
v_unused_2140_ = lean_ctor_get(v___x_2122_, 3);
lean_dec(v_unused_2140_);
v___x_2129_ = v___x_2122_;
v_isShared_2130_ = v_isSharedCheck_2139_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_diag_2127_);
lean_inc(v_zetaDeltaFVarIds_2126_);
lean_inc(v_cache_2125_);
lean_inc(v_mctx_2124_);
lean_dec(v___x_2122_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2139_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = l_Lean_PersistentArray_append___redArg(v_a_2100_, v_postponed_2123_);
lean_dec_ref(v_postponed_2123_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 3, v___x_2131_);
v___x_2133_ = v___x_2129_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_mctx_2124_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_cache_2125_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_zetaDeltaFVarIds_2126_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v_diag_2127_);
v___x_2133_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = lean_st_ref_set(v_a_2027_, v___x_2133_);
if (v_isShared_2108_ == 0)
{
v___x_2136_ = v___x_2107_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2105_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
else
{
lean_object* v_a_2142_; 
lean_dec(v_a_2100_);
v_a_2142_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v___x_2104_);
v_a_2060_ = v_a_2142_;
goto v___jp_2059_;
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_del_object(v___x_2034_);
lean_dec(v_a_2032_);
lean_dec_ref(v_s_2024_);
lean_dec_ref(v_t_2023_);
lean_dec(v_candidate_2022_);
v_a_2269_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2099_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2099_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
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
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_s_2024_);
lean_dec_ref(v_t_2023_);
lean_dec(v_candidate_2022_);
v_a_2283_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2031_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2031_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object* v_candidate_2291_, lean_object* v_t_2292_, lean_object* v_s_2293_, lean_object* v_mayPostpone_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
uint8_t v_mayPostpone_boxed_2300_; lean_object* v_res_2301_; 
v_mayPostpone_boxed_2300_ = lean_unbox(v_mayPostpone_2294_);
v_res_2301_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2291_, v_t_2292_, v_s_2293_, v_mayPostpone_boxed_2300_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2301_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = lean_unsigned_to_nat(32u);
v___x_2303_ = lean_mk_empty_array_with_capacity(v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2305_ = ((size_t)5ULL);
v___x_2306_ = lean_unsigned_to_nat(0u);
v___x_2307_ = lean_unsigned_to_nat(32u);
v___x_2308_ = lean_mk_empty_array_with_capacity(v___x_2307_);
v___x_2309_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0);
v___x_2310_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___x_2308_);
lean_ctor_set(v___x_2310_, 2, v___x_2306_);
lean_ctor_set(v___x_2310_, 3, v___x_2306_);
lean_ctor_set_usize(v___x_2310_, 4, v___x_2305_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; lean_object* v_traceState_2314_; lean_object* v_traces_2315_; lean_object* v___x_2316_; lean_object* v_traceState_2317_; lean_object* v_env_2318_; lean_object* v_nextMacroScope_2319_; lean_object* v_ngen_2320_; lean_object* v_auxDeclNGen_2321_; lean_object* v_cache_2322_; lean_object* v_messages_2323_; lean_object* v_infoState_2324_; lean_object* v_snapshotTasks_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2344_; 
v___x_2313_ = lean_st_ref_get(v___y_2311_);
v_traceState_2314_ = lean_ctor_get(v___x_2313_, 4);
lean_inc_ref(v_traceState_2314_);
lean_dec(v___x_2313_);
v_traces_2315_ = lean_ctor_get(v_traceState_2314_, 0);
lean_inc_ref(v_traces_2315_);
lean_dec_ref(v_traceState_2314_);
v___x_2316_ = lean_st_ref_take(v___y_2311_);
v_traceState_2317_ = lean_ctor_get(v___x_2316_, 4);
v_env_2318_ = lean_ctor_get(v___x_2316_, 0);
v_nextMacroScope_2319_ = lean_ctor_get(v___x_2316_, 1);
v_ngen_2320_ = lean_ctor_get(v___x_2316_, 2);
v_auxDeclNGen_2321_ = lean_ctor_get(v___x_2316_, 3);
v_cache_2322_ = lean_ctor_get(v___x_2316_, 5);
v_messages_2323_ = lean_ctor_get(v___x_2316_, 6);
v_infoState_2324_ = lean_ctor_get(v___x_2316_, 7);
v_snapshotTasks_2325_ = lean_ctor_get(v___x_2316_, 8);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2327_ = v___x_2316_;
v_isShared_2328_ = v_isSharedCheck_2344_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_snapshotTasks_2325_);
lean_inc(v_infoState_2324_);
lean_inc(v_messages_2323_);
lean_inc(v_cache_2322_);
lean_inc(v_traceState_2317_);
lean_inc(v_auxDeclNGen_2321_);
lean_inc(v_ngen_2320_);
lean_inc(v_nextMacroScope_2319_);
lean_inc(v_env_2318_);
lean_dec(v___x_2316_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2344_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
uint64_t v_tid_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2342_; 
v_tid_2329_ = lean_ctor_get_uint64(v_traceState_2317_, sizeof(void*)*1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_traceState_2317_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v_traceState_2317_, 0);
lean_dec(v_unused_2343_);
v___x_2331_ = v_traceState_2317_;
v_isShared_2332_ = v_isSharedCheck_2342_;
goto v_resetjp_2330_;
}
else
{
lean_dec(v_traceState_2317_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2342_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2333_);
lean_ctor_set_uint64(v_reuseFailAlloc_2341_, sizeof(void*)*1, v_tid_2329_);
v___x_2335_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 4, v___x_2335_);
v___x_2337_ = v___x_2327_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_env_2318_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_nextMacroScope_2319_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_ngen_2320_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_auxDeclNGen_2321_);
lean_ctor_set(v_reuseFailAlloc_2340_, 4, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2340_, 5, v_cache_2322_);
lean_ctor_set(v_reuseFailAlloc_2340_, 6, v_messages_2323_);
lean_ctor_set(v_reuseFailAlloc_2340_, 7, v_infoState_2324_);
lean_ctor_set(v_reuseFailAlloc_2340_, 8, v_snapshotTasks_2325_);
v___x_2337_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_st_ref_set(v___y_2311_, v___x_2337_);
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v_traces_2315_);
return v___x_2339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___boxed(lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2345_);
lean_dec(v___y_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2359_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object* v_opts_2360_, lean_object* v_opt_2361_){
_start:
{
lean_object* v_name_2362_; lean_object* v_defValue_2363_; lean_object* v_map_2364_; lean_object* v___x_2365_; 
v_name_2362_ = lean_ctor_get(v_opt_2361_, 0);
v_defValue_2363_ = lean_ctor_get(v_opt_2361_, 1);
v_map_2364_ = lean_ctor_get(v_opts_2360_, 0);
v___x_2365_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2364_, v_name_2362_);
if (lean_obj_tag(v___x_2365_) == 0)
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_unbox(v_defValue_2363_);
return v___x_2366_;
}
else
{
lean_object* v_val_2367_; 
v_val_2367_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_val_2367_);
lean_dec_ref(v___x_2365_);
if (lean_obj_tag(v_val_2367_) == 1)
{
uint8_t v_v_2368_; 
v_v_2368_ = lean_ctor_get_uint8(v_val_2367_, 0);
lean_dec_ref(v_val_2367_);
return v_v_2368_;
}
else
{
uint8_t v___x_2369_; 
lean_dec(v_val_2367_);
v___x_2369_ = lean_unbox(v_defValue_2363_);
return v___x_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object* v_opts_2370_, lean_object* v_opt_2371_){
_start:
{
uint8_t v_res_2372_; lean_object* v_r_2373_; 
v_res_2372_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2370_, v_opt_2371_);
lean_dec_ref(v_opt_2371_);
lean_dec_ref(v_opts_2370_);
v_r_2373_ = lean_box(v_res_2372_);
return v_r_2373_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0));
v___x_2376_ = l_Lean_stringToMessageData(v___x_2375_);
return v___x_2376_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2));
v___x_2379_ = l_Lean_stringToMessageData(v___x_2378_);
return v___x_2379_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4));
v___x_2382_ = l_Lean_stringToMessageData(v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object* v_candidate_2383_, lean_object* v_t_2384_, lean_object* v_s_2385_, lean_object* v_x_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2392_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1);
v___x_2393_ = l_Lean_MessageData_ofName(v_candidate_2383_);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = l_Lean_MessageData_ofExpr(v_t_2384_);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = l_Lean_MessageData_ofExpr(v_s_2385_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object* v_candidate_2404_, lean_object* v_t_2405_, lean_object* v_s_2406_, lean_object* v_x_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(v_candidate_2404_, v_t_2405_, v_s_2406_, v_x_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec_ref(v_x_2407_);
return v_res_2413_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(lean_object* v_e_2414_){
_start:
{
if (lean_obj_tag(v_e_2414_) == 0)
{
uint8_t v___x_2415_; 
v___x_2415_ = 2;
return v___x_2415_;
}
else
{
lean_object* v_a_2416_; uint8_t v___x_2417_; 
v_a_2416_ = lean_ctor_get(v_e_2414_, 0);
v___x_2417_ = lean_unbox(v_a_2416_);
if (v___x_2417_ == 0)
{
uint8_t v___x_2418_; 
v___x_2418_ = 1;
return v___x_2418_;
}
else
{
uint8_t v___x_2419_; 
v___x_2419_ = 0;
return v___x_2419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(lean_object* v_e_2420_){
_start:
{
uint8_t v_res_2421_; lean_object* v_r_2422_; 
v_res_2421_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_e_2420_);
lean_dec_ref(v_e_2420_);
v_r_2422_ = lean_box(v_res_2421_);
return v_r_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(lean_object* v_opts_2423_, lean_object* v_opt_2424_){
_start:
{
lean_object* v_name_2425_; lean_object* v_defValue_2426_; lean_object* v_map_2427_; lean_object* v___x_2428_; 
v_name_2425_ = lean_ctor_get(v_opt_2424_, 0);
v_defValue_2426_ = lean_ctor_get(v_opt_2424_, 1);
v_map_2427_ = lean_ctor_get(v_opts_2423_, 0);
v___x_2428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2427_, v_name_2425_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_inc(v_defValue_2426_);
return v_defValue_2426_;
}
else
{
lean_object* v_val_2429_; 
v_val_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_val_2429_);
lean_dec_ref(v___x_2428_);
if (lean_obj_tag(v_val_2429_) == 3)
{
lean_object* v_v_2430_; 
v_v_2430_ = lean_ctor_get(v_val_2429_, 0);
lean_inc(v_v_2430_);
lean_dec_ref(v_val_2429_);
return v_v_2430_;
}
else
{
lean_dec(v_val_2429_);
lean_inc(v_defValue_2426_);
return v_defValue_2426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(lean_object* v_opts_2431_, lean_object* v_opt_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2431_, v_opt_2432_);
lean_dec_ref(v_opt_2432_);
lean_dec_ref(v_opts_2431_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(lean_object* v_x_2434_){
_start:
{
if (lean_obj_tag(v_x_2434_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_a_2436_ = lean_ctor_get(v_x_2434_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_x_2434_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v_x_2434_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v_x_2434_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 1);
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
v_a_2444_ = lean_ctor_get(v_x_2434_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_x_2434_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v_x_2434_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v_x_2434_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set_tag(v___x_2446_, 0);
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg___boxed(lean_object* v_x_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_x_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(size_t v_sz_2455_, size_t v_i_2456_, lean_object* v_bs_2457_){
_start:
{
uint8_t v___x_2458_; 
v___x_2458_ = lean_usize_dec_lt(v_i_2456_, v_sz_2455_);
if (v___x_2458_ == 0)
{
return v_bs_2457_;
}
else
{
lean_object* v_v_2459_; lean_object* v_msg_2460_; lean_object* v___x_2461_; lean_object* v_bs_x27_2462_; size_t v___x_2463_; size_t v___x_2464_; lean_object* v___x_2465_; 
v_v_2459_ = lean_array_uget_borrowed(v_bs_2457_, v_i_2456_);
v_msg_2460_ = lean_ctor_get(v_v_2459_, 1);
lean_inc_ref(v_msg_2460_);
v___x_2461_ = lean_unsigned_to_nat(0u);
v_bs_x27_2462_ = lean_array_uset(v_bs_2457_, v_i_2456_, v___x_2461_);
v___x_2463_ = ((size_t)1ULL);
v___x_2464_ = lean_usize_add(v_i_2456_, v___x_2463_);
v___x_2465_ = lean_array_uset(v_bs_x27_2462_, v_i_2456_, v_msg_2460_);
v_i_2456_ = v___x_2464_;
v_bs_2457_ = v___x_2465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9___boxed(lean_object* v_sz_2467_, lean_object* v_i_2468_, lean_object* v_bs_2469_){
_start:
{
size_t v_sz_boxed_2470_; size_t v_i_boxed_2471_; lean_object* v_res_2472_; 
v_sz_boxed_2470_ = lean_unbox_usize(v_sz_2467_);
lean_dec(v_sz_2467_);
v_i_boxed_2471_ = lean_unbox_usize(v_i_2468_);
lean_dec(v_i_2468_);
v_res_2472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(v_sz_boxed_2470_, v_i_boxed_2471_, v_bs_2469_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(lean_object* v_oldTraces_2473_, lean_object* v_data_2474_, lean_object* v_ref_2475_, lean_object* v_msg_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_fileName_2482_; lean_object* v_fileMap_2483_; lean_object* v_options_2484_; lean_object* v_currRecDepth_2485_; lean_object* v_maxRecDepth_2486_; lean_object* v_ref_2487_; lean_object* v_currNamespace_2488_; lean_object* v_openDecls_2489_; lean_object* v_initHeartbeats_2490_; lean_object* v_maxHeartbeats_2491_; lean_object* v_quotContext_2492_; lean_object* v_currMacroScope_2493_; uint8_t v_diag_2494_; lean_object* v_cancelTk_x3f_2495_; uint8_t v_suppressElabErrors_2496_; lean_object* v_inheritedTraceOptions_2497_; lean_object* v___x_2498_; lean_object* v_traceState_2499_; lean_object* v_traces_2500_; lean_object* v_ref_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; size_t v_sz_2504_; size_t v___x_2505_; lean_object* v___x_2506_; lean_object* v_msg_2507_; lean_object* v___x_2508_; lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2546_; 
v_fileName_2482_ = lean_ctor_get(v___y_2479_, 0);
v_fileMap_2483_ = lean_ctor_get(v___y_2479_, 1);
v_options_2484_ = lean_ctor_get(v___y_2479_, 2);
v_currRecDepth_2485_ = lean_ctor_get(v___y_2479_, 3);
v_maxRecDepth_2486_ = lean_ctor_get(v___y_2479_, 4);
v_ref_2487_ = lean_ctor_get(v___y_2479_, 5);
v_currNamespace_2488_ = lean_ctor_get(v___y_2479_, 6);
v_openDecls_2489_ = lean_ctor_get(v___y_2479_, 7);
v_initHeartbeats_2490_ = lean_ctor_get(v___y_2479_, 8);
v_maxHeartbeats_2491_ = lean_ctor_get(v___y_2479_, 9);
v_quotContext_2492_ = lean_ctor_get(v___y_2479_, 10);
v_currMacroScope_2493_ = lean_ctor_get(v___y_2479_, 11);
v_diag_2494_ = lean_ctor_get_uint8(v___y_2479_, sizeof(void*)*14);
v_cancelTk_x3f_2495_ = lean_ctor_get(v___y_2479_, 12);
v_suppressElabErrors_2496_ = lean_ctor_get_uint8(v___y_2479_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2497_ = lean_ctor_get(v___y_2479_, 13);
v___x_2498_ = lean_st_ref_get(v___y_2480_);
v_traceState_2499_ = lean_ctor_get(v___x_2498_, 4);
lean_inc_ref(v_traceState_2499_);
lean_dec(v___x_2498_);
v_traces_2500_ = lean_ctor_get(v_traceState_2499_, 0);
lean_inc_ref(v_traces_2500_);
lean_dec_ref(v_traceState_2499_);
v_ref_2501_ = l_Lean_replaceRef(v_ref_2475_, v_ref_2487_);
lean_inc_ref(v_inheritedTraceOptions_2497_);
lean_inc(v_cancelTk_x3f_2495_);
lean_inc(v_currMacroScope_2493_);
lean_inc(v_quotContext_2492_);
lean_inc(v_maxHeartbeats_2491_);
lean_inc(v_initHeartbeats_2490_);
lean_inc(v_openDecls_2489_);
lean_inc(v_currNamespace_2488_);
lean_inc(v_maxRecDepth_2486_);
lean_inc(v_currRecDepth_2485_);
lean_inc_ref(v_options_2484_);
lean_inc_ref(v_fileMap_2483_);
lean_inc_ref(v_fileName_2482_);
v___x_2502_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2502_, 0, v_fileName_2482_);
lean_ctor_set(v___x_2502_, 1, v_fileMap_2483_);
lean_ctor_set(v___x_2502_, 2, v_options_2484_);
lean_ctor_set(v___x_2502_, 3, v_currRecDepth_2485_);
lean_ctor_set(v___x_2502_, 4, v_maxRecDepth_2486_);
lean_ctor_set(v___x_2502_, 5, v_ref_2501_);
lean_ctor_set(v___x_2502_, 6, v_currNamespace_2488_);
lean_ctor_set(v___x_2502_, 7, v_openDecls_2489_);
lean_ctor_set(v___x_2502_, 8, v_initHeartbeats_2490_);
lean_ctor_set(v___x_2502_, 9, v_maxHeartbeats_2491_);
lean_ctor_set(v___x_2502_, 10, v_quotContext_2492_);
lean_ctor_set(v___x_2502_, 11, v_currMacroScope_2493_);
lean_ctor_set(v___x_2502_, 12, v_cancelTk_x3f_2495_);
lean_ctor_set(v___x_2502_, 13, v_inheritedTraceOptions_2497_);
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*14, v_diag_2494_);
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*14 + 1, v_suppressElabErrors_2496_);
v___x_2503_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2500_);
lean_dec_ref(v_traces_2500_);
v_sz_2504_ = lean_array_size(v___x_2503_);
v___x_2505_ = ((size_t)0ULL);
v___x_2506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(v_sz_2504_, v___x_2505_, v___x_2503_);
v_msg_2507_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2507_, 0, v_data_2474_);
lean_ctor_set(v_msg_2507_, 1, v_msg_2476_);
lean_ctor_set(v_msg_2507_, 2, v___x_2506_);
v___x_2508_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2507_, v___y_2477_, v___y_2478_, v___x_2502_, v___y_2480_);
lean_dec_ref(v___x_2502_);
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2546_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2546_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v_traceState_2514_; lean_object* v_env_2515_; lean_object* v_nextMacroScope_2516_; lean_object* v_ngen_2517_; lean_object* v_auxDeclNGen_2518_; lean_object* v_cache_2519_; lean_object* v_messages_2520_; lean_object* v_infoState_2521_; lean_object* v_snapshotTasks_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2545_; 
v___x_2513_ = lean_st_ref_take(v___y_2480_);
v_traceState_2514_ = lean_ctor_get(v___x_2513_, 4);
v_env_2515_ = lean_ctor_get(v___x_2513_, 0);
v_nextMacroScope_2516_ = lean_ctor_get(v___x_2513_, 1);
v_ngen_2517_ = lean_ctor_get(v___x_2513_, 2);
v_auxDeclNGen_2518_ = lean_ctor_get(v___x_2513_, 3);
v_cache_2519_ = lean_ctor_get(v___x_2513_, 5);
v_messages_2520_ = lean_ctor_get(v___x_2513_, 6);
v_infoState_2521_ = lean_ctor_get(v___x_2513_, 7);
v_snapshotTasks_2522_ = lean_ctor_get(v___x_2513_, 8);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2524_ = v___x_2513_;
v_isShared_2525_ = v_isSharedCheck_2545_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_snapshotTasks_2522_);
lean_inc(v_infoState_2521_);
lean_inc(v_messages_2520_);
lean_inc(v_cache_2519_);
lean_inc(v_traceState_2514_);
lean_inc(v_auxDeclNGen_2518_);
lean_inc(v_ngen_2517_);
lean_inc(v_nextMacroScope_2516_);
lean_inc(v_env_2515_);
lean_dec(v___x_2513_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2545_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
uint64_t v_tid_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2543_; 
v_tid_2526_ = lean_ctor_get_uint64(v_traceState_2514_, sizeof(void*)*1);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_traceState_2514_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v_traceState_2514_, 0);
lean_dec(v_unused_2544_);
v___x_2528_ = v_traceState_2514_;
v_isShared_2529_ = v_isSharedCheck_2543_;
goto v_resetjp_2527_;
}
else
{
lean_dec(v_traceState_2514_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2543_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_ref_2475_);
lean_ctor_set(v___x_2530_, 1, v_a_2509_);
v___x_2531_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2473_, v___x_2530_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2531_);
v___x_2533_ = v___x_2528_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2531_);
lean_ctor_set_uint64(v_reuseFailAlloc_2542_, sizeof(void*)*1, v_tid_2526_);
v___x_2533_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2535_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 4, v___x_2533_);
v___x_2535_ = v___x_2524_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_env_2515_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_nextMacroScope_2516_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_ngen_2517_);
lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_auxDeclNGen_2518_);
lean_ctor_set(v_reuseFailAlloc_2541_, 4, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2541_, 5, v_cache_2519_);
lean_ctor_set(v_reuseFailAlloc_2541_, 6, v_messages_2520_);
lean_ctor_set(v_reuseFailAlloc_2541_, 7, v_infoState_2521_);
lean_ctor_set(v_reuseFailAlloc_2541_, 8, v_snapshotTasks_2522_);
v___x_2535_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2536_ = lean_st_ref_set(v___y_2480_, v___x_2535_);
v___x_2537_ = lean_box(0);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2537_);
v___x_2539_ = v___x_2511_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(lean_object* v_oldTraces_2547_, lean_object* v_data_2548_, lean_object* v_ref_2549_, lean_object* v_msg_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_oldTraces_2547_, v_data_2548_, v_ref_2549_, v_msg_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2556_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0));
v___x_2559_ = l_Lean_stringToMessageData(v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2));
v___x_2562_ = l_Lean_stringToMessageData(v___x_2561_);
return v___x_2562_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4(void){
_start:
{
lean_object* v___x_2563_; double v___x_2564_; 
v___x_2563_ = lean_unsigned_to_nat(1000u);
v___x_2564_ = lean_float_of_nat(v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object* v_cls_2565_, uint8_t v_collapsed_2566_, lean_object* v_tag_2567_, lean_object* v_opts_2568_, uint8_t v_clsEnabled_2569_, lean_object* v_oldTraces_2570_, lean_object* v_msg_2571_, lean_object* v_resStartStop_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_fst_2578_; lean_object* v_snd_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2677_; 
v_fst_2578_ = lean_ctor_get(v_resStartStop_2572_, 0);
v_snd_2579_ = lean_ctor_get(v_resStartStop_2572_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_resStartStop_2572_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2581_ = v_resStartStop_2572_;
v_isShared_2582_ = v_isSharedCheck_2677_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_snd_2579_);
lean_inc(v_fst_2578_);
lean_dec(v_resStartStop_2572_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2677_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v_data_2586_; lean_object* v_fst_2597_; lean_object* v_snd_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2676_; 
v_fst_2597_ = lean_ctor_get(v_snd_2579_, 0);
v_snd_2598_ = lean_ctor_get(v_snd_2579_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v_snd_2579_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2600_ = v_snd_2579_;
v_isShared_2601_ = v_isSharedCheck_2676_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_snd_2598_);
lean_inc(v_fst_2597_);
lean_dec(v_snd_2579_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2676_;
goto v_resetjp_2599_;
}
v___jp_2583_:
{
lean_object* v___x_2587_; 
lean_inc(v___y_2584_);
v___x_2587_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_oldTraces_2570_, v_data_2586_, v___y_2584_, v___y_2585_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2588_; 
lean_dec_ref(v___x_2587_);
v___x_2588_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_fst_2578_);
return v___x_2588_;
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v_fst_2578_);
v_a_2589_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2587_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2587_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v___y_2605_; lean_object* v_a_2606_; uint8_t v___y_2630_; double v___y_2661_; 
v___x_2602_ = l_Lean_trace_profiler;
v___x_2603_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2568_, v___x_2602_);
if (v___x_2603_ == 0)
{
v___y_2630_ = v___x_2603_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2667_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2568_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; double v___x_2670_; double v___x_2671_; double v___x_2672_; 
v___x_2668_ = l_Lean_trace_profiler_threshold;
v___x_2669_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2568_, v___x_2668_);
v___x_2670_ = lean_float_of_nat(v___x_2669_);
v___x_2671_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4);
v___x_2672_ = lean_float_div(v___x_2670_, v___x_2671_);
v___y_2661_ = v___x_2672_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; double v___x_2675_; 
v___x_2673_ = l_Lean_trace_profiler_threshold;
v___x_2674_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2568_, v___x_2673_);
v___x_2675_ = lean_float_of_nat(v___x_2674_);
v___y_2661_ = v___x_2675_;
goto v___jp_2660_;
}
}
v___jp_2604_:
{
uint8_t v_result_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v_result_2607_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_fst_2578_);
v___x_2608_ = l_Lean_TraceResult_toEmoji(v_result_2607_);
v___x_2609_ = l_Lean_stringToMessageData(v___x_2608_);
v___x_2610_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1);
if (v_isShared_2601_ == 0)
{
lean_ctor_set_tag(v___x_2600_, 7);
lean_ctor_set(v___x_2600_, 1, v___x_2610_);
lean_ctor_set(v___x_2600_, 0, v___x_2609_);
v___x_2612_ = v___x_2600_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v_m_2614_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 7);
lean_ctor_set(v___x_2581_, 1, v_a_2606_);
lean_ctor_set(v___x_2581_, 0, v___x_2612_);
v_m_2614_ = v___x_2581_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_a_2606_);
v_m_2614_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; double v___x_2617_; lean_object* v_data_2618_; 
v___x_2615_ = lean_box(v_result_2607_);
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
v___x_2617_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
lean_inc_ref(v_tag_2567_);
lean_inc_ref(v___x_2616_);
lean_inc(v_cls_2565_);
v_data_2618_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2618_, 0, v_cls_2565_);
lean_ctor_set(v_data_2618_, 1, v___x_2616_);
lean_ctor_set(v_data_2618_, 2, v_tag_2567_);
lean_ctor_set_float(v_data_2618_, sizeof(void*)*3, v___x_2617_);
lean_ctor_set_float(v_data_2618_, sizeof(void*)*3 + 8, v___x_2617_);
lean_ctor_set_uint8(v_data_2618_, sizeof(void*)*3 + 16, v_collapsed_2566_);
if (v___x_2603_ == 0)
{
lean_dec_ref(v___x_2616_);
lean_dec(v_snd_2598_);
lean_dec(v_fst_2597_);
lean_dec_ref(v_tag_2567_);
lean_dec(v_cls_2565_);
v___y_2584_ = v___y_2605_;
v___y_2585_ = v_m_2614_;
v_data_2586_ = v_data_2618_;
goto v___jp_2583_;
}
else
{
lean_object* v_data_2619_; double v___x_2620_; double v___x_2621_; 
lean_dec_ref(v_data_2618_);
v_data_2619_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2619_, 0, v_cls_2565_);
lean_ctor_set(v_data_2619_, 1, v___x_2616_);
lean_ctor_set(v_data_2619_, 2, v_tag_2567_);
v___x_2620_ = lean_unbox_float(v_fst_2597_);
lean_dec(v_fst_2597_);
lean_ctor_set_float(v_data_2619_, sizeof(void*)*3, v___x_2620_);
v___x_2621_ = lean_unbox_float(v_snd_2598_);
lean_dec(v_snd_2598_);
lean_ctor_set_float(v_data_2619_, sizeof(void*)*3 + 8, v___x_2621_);
lean_ctor_set_uint8(v_data_2619_, sizeof(void*)*3 + 16, v_collapsed_2566_);
v___y_2584_ = v___y_2605_;
v___y_2585_ = v_m_2614_;
v_data_2586_ = v_data_2619_;
goto v___jp_2583_;
}
}
}
}
v___jp_2624_:
{
lean_object* v_ref_2625_; lean_object* v___x_2626_; 
v_ref_2625_ = lean_ctor_get(v___y_2575_, 5);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc_ref(v___y_2573_);
lean_inc(v_fst_2578_);
v___x_2626_ = lean_apply_6(v_msg_2571_, v_fst_2578_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, lean_box(0));
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref(v___x_2626_);
v___y_2605_ = v_ref_2625_;
v_a_2606_ = v_a_2627_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2628_; 
lean_dec_ref(v___x_2626_);
v___x_2628_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3);
v___y_2605_ = v_ref_2625_;
v_a_2606_ = v___x_2628_;
goto v___jp_2604_;
}
}
v___jp_2629_:
{
if (v_clsEnabled_2569_ == 0)
{
if (v___y_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v_traceState_2632_; lean_object* v_env_2633_; lean_object* v_nextMacroScope_2634_; lean_object* v_ngen_2635_; lean_object* v_auxDeclNGen_2636_; lean_object* v_cache_2637_; lean_object* v_messages_2638_; lean_object* v_infoState_2639_; lean_object* v_snapshotTasks_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2659_; 
lean_del_object(v___x_2600_);
lean_dec(v_snd_2598_);
lean_dec(v_fst_2597_);
lean_del_object(v___x_2581_);
lean_dec_ref(v_msg_2571_);
lean_dec_ref(v_tag_2567_);
lean_dec(v_cls_2565_);
v___x_2631_ = lean_st_ref_take(v___y_2576_);
v_traceState_2632_ = lean_ctor_get(v___x_2631_, 4);
v_env_2633_ = lean_ctor_get(v___x_2631_, 0);
v_nextMacroScope_2634_ = lean_ctor_get(v___x_2631_, 1);
v_ngen_2635_ = lean_ctor_get(v___x_2631_, 2);
v_auxDeclNGen_2636_ = lean_ctor_get(v___x_2631_, 3);
v_cache_2637_ = lean_ctor_get(v___x_2631_, 5);
v_messages_2638_ = lean_ctor_get(v___x_2631_, 6);
v_infoState_2639_ = lean_ctor_get(v___x_2631_, 7);
v_snapshotTasks_2640_ = lean_ctor_get(v___x_2631_, 8);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2642_ = v___x_2631_;
v_isShared_2643_ = v_isSharedCheck_2659_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_snapshotTasks_2640_);
lean_inc(v_infoState_2639_);
lean_inc(v_messages_2638_);
lean_inc(v_cache_2637_);
lean_inc(v_traceState_2632_);
lean_inc(v_auxDeclNGen_2636_);
lean_inc(v_ngen_2635_);
lean_inc(v_nextMacroScope_2634_);
lean_inc(v_env_2633_);
lean_dec(v___x_2631_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2659_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
uint64_t v_tid_2644_; lean_object* v_traces_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2658_; 
v_tid_2644_ = lean_ctor_get_uint64(v_traceState_2632_, sizeof(void*)*1);
v_traces_2645_ = lean_ctor_get(v_traceState_2632_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_traceState_2632_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2647_ = v_traceState_2632_;
v_isShared_2648_ = v_isSharedCheck_2658_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_traces_2645_);
lean_dec(v_traceState_2632_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2658_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2570_, v_traces_2645_);
lean_dec_ref(v_traces_2645_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2649_);
lean_ctor_set_uint64(v_reuseFailAlloc_2657_, sizeof(void*)*1, v_tid_2644_);
v___x_2651_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2653_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 4, v___x_2651_);
v___x_2653_ = v___x_2642_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_env_2633_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_nextMacroScope_2634_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_ngen_2635_);
lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_auxDeclNGen_2636_);
lean_ctor_set(v_reuseFailAlloc_2656_, 4, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2656_, 5, v_cache_2637_);
lean_ctor_set(v_reuseFailAlloc_2656_, 6, v_messages_2638_);
lean_ctor_set(v_reuseFailAlloc_2656_, 7, v_infoState_2639_);
lean_ctor_set(v_reuseFailAlloc_2656_, 8, v_snapshotTasks_2640_);
v___x_2653_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_st_ref_set(v___y_2576_, v___x_2653_);
v___x_2655_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_fst_2578_);
return v___x_2655_;
}
}
}
}
}
else
{
goto v___jp_2624_;
}
}
else
{
goto v___jp_2624_;
}
}
v___jp_2660_:
{
double v___x_2662_; double v___x_2663_; double v___x_2664_; uint8_t v___x_2665_; 
v___x_2662_ = lean_unbox_float(v_snd_2598_);
v___x_2663_ = lean_unbox_float(v_fst_2597_);
v___x_2664_ = lean_float_sub(v___x_2662_, v___x_2663_);
v___x_2665_ = lean_float_decLt(v___y_2661_, v___x_2664_);
v___y_2630_ = v___x_2665_;
goto v___jp_2629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object* v_cls_2678_, lean_object* v_collapsed_2679_, lean_object* v_tag_2680_, lean_object* v_opts_2681_, lean_object* v_clsEnabled_2682_, lean_object* v_oldTraces_2683_, lean_object* v_msg_2684_, lean_object* v_resStartStop_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v_collapsed_boxed_2691_; uint8_t v_clsEnabled_boxed_2692_; lean_object* v_res_2693_; 
v_collapsed_boxed_2691_ = lean_unbox(v_collapsed_2679_);
v_clsEnabled_boxed_2692_ = lean_unbox(v_clsEnabled_2682_);
v_res_2693_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2678_, v_collapsed_boxed_2691_, v_tag_2680_, v_opts_2681_, v_clsEnabled_boxed_2692_, v_oldTraces_2683_, v_msg_2684_, v_resStartStop_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_opts_2681_);
return v_res_2693_;
}
}
static double _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0(void){
_start:
{
lean_object* v___x_2694_; double v___x_2695_; 
v___x_2694_ = lean_unsigned_to_nat(1000000000u);
v___x_2695_ = lean_float_of_nat(v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object* v_t_2696_, lean_object* v_s_2697_, lean_object* v_candidate_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_options_2704_; lean_object* v_inheritedTraceOptions_2705_; uint8_t v_hasTrace_2706_; uint8_t v___x_2707_; 
v_options_2704_ = lean_ctor_get(v_a_2701_, 2);
v_inheritedTraceOptions_2705_ = lean_ctor_get(v_a_2701_, 13);
v_hasTrace_2706_ = lean_ctor_get_uint8(v_options_2704_, sizeof(void*)*1);
v___x_2707_ = 1;
if (v_hasTrace_2706_ == 0)
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2698_, v_t_2696_, v_s_2697_, v___x_2707_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
return v___x_2708_;
}
else
{
lean_object* v___f_2709_; lean_object* v_cls_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v_a_2717_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v_a_2732_; 
lean_inc_ref(v_s_2697_);
lean_inc_ref(v_t_2696_);
lean_inc(v_candidate_2698_);
v___f_2709_ = lean_alloc_closure((void*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2709_, 0, v_candidate_2698_);
lean_closure_set(v___f_2709_, 1, v_t_2696_);
lean_closure_set(v___f_2709_, 2, v_s_2697_);
v_cls_2710_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2711_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_2712_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2713_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2705_, v_options_2704_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2782_; uint8_t v___x_2783_; 
v___x_2782_ = l_Lean_trace_profiler;
v___x_2783_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2704_, v___x_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
lean_dec_ref(v___f_2709_);
v___x_2784_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2698_, v_t_2696_, v_s_2697_, v___x_2707_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
return v___x_2784_;
}
else
{
goto v___jp_2741_;
}
}
else
{
goto v___jp_2741_;
}
v___jp_2714_:
{
lean_object* v___x_2718_; double v___x_2719_; double v___x_2720_; double v___x_2721_; double v___x_2722_; double v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2718_ = lean_io_mono_nanos_now();
v___x_2719_ = lean_float_of_nat(v___y_2715_);
v___x_2720_ = lean_float_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0);
v___x_2721_ = lean_float_div(v___x_2719_, v___x_2720_);
v___x_2722_ = lean_float_of_nat(v___x_2718_);
v___x_2723_ = lean_float_div(v___x_2722_, v___x_2720_);
v___x_2724_ = lean_box_float(v___x_2721_);
v___x_2725_ = lean_box_float(v___x_2723_);
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_a_2717_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2710_, v___x_2707_, v___x_2711_, v_options_2704_, v___x_2713_, v___y_2716_, v___f_2709_, v___x_2727_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
return v___x_2728_;
}
v___jp_2729_:
{
lean_object* v___x_2733_; double v___x_2734_; double v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2733_ = lean_io_get_num_heartbeats();
v___x_2734_ = lean_float_of_nat(v___y_2730_);
v___x_2735_ = lean_float_of_nat(v___x_2733_);
v___x_2736_ = lean_box_float(v___x_2734_);
v___x_2737_ = lean_box_float(v___x_2735_);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2739_, 0, v_a_2732_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2710_, v___x_2707_, v___x_2711_, v_options_2704_, v___x_2713_, v___y_2731_, v___f_2709_, v___x_2739_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
return v___x_2740_;
}
v___jp_2741_:
{
lean_object* v___x_2742_; lean_object* v_a_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v___x_2742_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v_a_2702_);
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v___x_2742_);
v___x_2744_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2745_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2704_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_io_mono_nanos_now();
v___x_2747_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2698_, v_t_2696_, v_s_2697_, v___x_2707_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 1);
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
v___y_2715_ = v___x_2746_;
v___y_2716_ = v_a_2743_;
v_a_2717_ = v___x_2753_;
goto v___jp_2714_;
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
v_a_2756_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2747_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2747_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set_tag(v___x_2758_, 0);
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
v___y_2715_ = v___x_2746_;
v___y_2716_ = v_a_2743_;
v_a_2717_ = v___x_2761_;
goto v___jp_2714_;
}
}
}
}
else
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_io_get_num_heartbeats();
v___x_2765_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2698_, v_t_2696_, v_s_2697_, v___x_2707_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set_tag(v___x_2768_, 1);
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
v___y_2730_ = v___x_2764_;
v___y_2731_ = v_a_2743_;
v_a_2732_ = v___x_2771_;
goto v___jp_2729_;
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
v_a_2774_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2765_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2765_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 0);
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
v___y_2730_ = v___x_2764_;
v___y_2731_ = v_a_2743_;
v_a_2732_ = v___x_2779_;
goto v___jp_2729_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object* v_t_2785_, lean_object* v_s_2786_, lean_object* v_candidate_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2785_, v_s_2786_, v_candidate_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object* v_as_2794_, lean_object* v_as_x27_2795_, lean_object* v_b_2796_, lean_object* v_a_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2795_, v_b_2796_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object* v_as_2804_, lean_object* v_as_x27_2805_, lean_object* v_b_2806_, lean_object* v_a_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(v_as_2804_, v_as_x27_2805_, v_b_2806_, v_a_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v_as_x27_2805_);
lean_dec(v_as_2804_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(lean_object* v_00_u03b1_2814_, lean_object* v_x_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_x_2815_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2822_, lean_object* v_x_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_00_u03b1_2822_, v_x_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(lean_object* v_t_2830_, lean_object* v_s_2831_, uint8_t v___x_2832_, lean_object* v_as_2833_, size_t v_sz_2834_, size_t v_i_2835_, lean_object* v_b_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
uint8_t v___x_2842_; 
v___x_2842_ = lean_usize_dec_lt(v_i_2835_, v_sz_2834_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; 
lean_dec_ref(v_s_2831_);
lean_dec_ref(v_t_2830_);
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v_b_2836_);
return v___x_2843_;
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2845_; 
lean_dec_ref(v_b_2836_);
v_a_2844_ = lean_array_uget_borrowed(v_as_2833_, v_i_2835_);
lean_inc(v_a_2844_);
lean_inc_ref(v_s_2831_);
lean_inc_ref(v_t_2830_);
v___x_2845_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2830_, v_s_2831_, v_a_2844_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2862_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2862_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2862_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2850_ = lean_box(0);
v___x_2851_ = lean_unbox(v_a_2846_);
lean_dec(v_a_2846_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; size_t v___x_2853_; size_t v___x_2854_; 
lean_del_object(v___x_2848_);
v___x_2852_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v___x_2853_ = ((size_t)1ULL);
v___x_2854_ = lean_usize_add(v_i_2835_, v___x_2853_);
v_i_2835_ = v___x_2854_;
v_b_2836_ = v___x_2852_;
goto _start;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
lean_dec_ref(v_s_2831_);
lean_dec_ref(v_t_2830_);
v___x_2856_ = lean_box(v___x_2832_);
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
v___x_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v___x_2850_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2858_);
v___x_2860_ = v___x_2848_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec_ref(v_s_2831_);
lean_dec_ref(v_t_2830_);
v_a_2863_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2845_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2845_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object* v_t_2871_, lean_object* v_s_2872_, lean_object* v___x_2873_, lean_object* v_as_2874_, lean_object* v_sz_2875_, lean_object* v_i_2876_, lean_object* v_b_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
uint8_t v___x_3586__boxed_2883_; size_t v_sz_boxed_2884_; size_t v_i_boxed_2885_; lean_object* v_res_2886_; 
v___x_3586__boxed_2883_ = lean_unbox(v___x_2873_);
v_sz_boxed_2884_ = lean_unbox_usize(v_sz_2875_);
lean_dec(v_sz_2875_);
v_i_boxed_2885_ = lean_unbox_usize(v_i_2876_);
lean_dec(v_i_2876_);
v_res_2886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2871_, v_s_2872_, v___x_3586__boxed_2883_, v_as_2874_, v_sz_boxed_2884_, v_i_boxed_2885_, v_b_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec_ref(v_as_2874_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* v_t_2887_, lean_object* v_s_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v_options_2966_; uint8_t v_hasTrace_2967_; 
v_options_2966_ = lean_ctor_get(v_a_2891_, 2);
v_hasTrace_2967_ = lean_ctor_get_uint8(v_options_2966_, sizeof(void*)*1);
if (v_hasTrace_2967_ == 0)
{
v___y_2895_ = v_a_2889_;
v___y_2896_ = v_a_2890_;
v___y_2897_ = v_a_2891_;
v___y_2898_ = v_a_2892_;
goto v___jp_2894_;
}
else
{
lean_object* v_inheritedTraceOptions_2968_; lean_object* v_cls_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v_inheritedTraceOptions_2968_ = lean_ctor_get(v_a_2891_, 13);
v_cls_2969_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2970_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2968_, v_options_2966_, v___x_2970_);
if (v___x_2971_ == 0)
{
v___y_2895_ = v_a_2889_;
v___y_2896_ = v_a_2890_;
v___y_2897_ = v_a_2891_;
v___y_2898_ = v_a_2892_;
goto v___jp_2894_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_inc_ref(v_t_2887_);
v___x_2972_ = l_Lean_MessageData_ofExpr(v_t_2887_);
v___x_2973_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
lean_inc_ref(v_s_2888_);
v___x_2975_ = l_Lean_MessageData_ofExpr(v_s_2888_);
v___x_2976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2974_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2969_, v___x_2976_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_dec_ref(v___x_2977_);
v___y_2895_ = v_a_2889_;
v___y_2896_ = v_a_2890_;
v___y_2897_ = v_a_2891_;
v___y_2898_ = v_a_2892_;
goto v___jp_2894_;
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec_ref(v_s_2888_);
lean_dec_ref(v_t_2887_);
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2977_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2977_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
v___jp_2894_:
{
lean_object* v___x_2899_; uint8_t v_unificationHints_2900_; 
v___x_2899_ = l_Lean_Meta_Context_config(v___y_2895_);
v_unificationHints_2900_ = lean_ctor_get_uint8(v___x_2899_, 5);
lean_dec_ref(v___x_2899_);
if (v_unificationHints_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec_ref(v_s_2888_);
lean_dec_ref(v_t_2887_);
v___x_2901_ = lean_box(v_unificationHints_2900_);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
else
{
uint8_t v___x_2903_; 
v___x_2903_ = l_Lean_Expr_isMVar(v_t_2887_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v_env_2905_; lean_object* v___x_2906_; lean_object* v_ext_2907_; lean_object* v_toEnvExtension_2908_; lean_object* v_asyncMode_2909_; lean_object* v___x_2910_; lean_object* v_config_2911_; uint8_t v_trackZetaDelta_2912_; lean_object* v_zetaDeltaSet_2913_; lean_object* v_lctx_2914_; lean_object* v_localInstances_2915_; lean_object* v_defEqCtx_x3f_2916_; lean_object* v_synthPendingDepth_2917_; lean_object* v_canUnfold_x3f_2918_; uint8_t v_univApprox_2919_; uint8_t v_inTypeClassResolution_2920_; uint8_t v_cacheInferType_2921_; uint64_t v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2904_ = lean_st_ref_get(v___y_2898_);
v_env_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc_ref(v_env_2905_);
lean_dec(v___x_2904_);
v___x_2906_ = l_Lean_Meta_unificationHintExtension;
v_ext_2907_ = lean_ctor_get(v___x_2906_, 1);
v_toEnvExtension_2908_ = lean_ctor_get(v_ext_2907_, 0);
v_asyncMode_2909_ = lean_ctor_get(v_toEnvExtension_2908_, 2);
v___x_2910_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_2911_ = lean_ctor_get(v___x_2910_, 0);
v_trackZetaDelta_2912_ = lean_ctor_get_uint8(v___y_2895_, sizeof(void*)*7);
v_zetaDeltaSet_2913_ = lean_ctor_get(v___y_2895_, 1);
v_lctx_2914_ = lean_ctor_get(v___y_2895_, 2);
v_localInstances_2915_ = lean_ctor_get(v___y_2895_, 3);
v_defEqCtx_x3f_2916_ = lean_ctor_get(v___y_2895_, 4);
v_synthPendingDepth_2917_ = lean_ctor_get(v___y_2895_, 5);
v_canUnfold_x3f_2918_ = lean_ctor_get(v___y_2895_, 6);
v_univApprox_2919_ = lean_ctor_get_uint8(v___y_2895_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2920_ = lean_ctor_get_uint8(v___y_2895_, sizeof(void*)*7 + 2);
v_cacheInferType_2921_ = lean_ctor_get_uint8(v___y_2895_, sizeof(void*)*7 + 3);
v___x_2922_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2911_);
v___x_2923_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___x_2924_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2923_, v___x_2906_, v_env_2905_, v_asyncMode_2909_);
lean_inc_ref(v_config_2911_);
v___x_2925_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2925_, 0, v_config_2911_);
lean_ctor_set_uint64(v___x_2925_, sizeof(void*)*1, v___x_2922_);
lean_inc(v_canUnfold_x3f_2918_);
lean_inc(v_synthPendingDepth_2917_);
lean_inc(v_defEqCtx_x3f_2916_);
lean_inc_ref(v_localInstances_2915_);
lean_inc_ref(v_lctx_2914_);
lean_inc(v_zetaDeltaSet_2913_);
v___x_2926_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v_zetaDeltaSet_2913_);
lean_ctor_set(v___x_2926_, 2, v_lctx_2914_);
lean_ctor_set(v___x_2926_, 3, v_localInstances_2915_);
lean_ctor_set(v___x_2926_, 4, v_defEqCtx_x3f_2916_);
lean_ctor_set(v___x_2926_, 5, v_synthPendingDepth_2917_);
lean_ctor_set(v___x_2926_, 6, v_canUnfold_x3f_2918_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*7, v_trackZetaDelta_2912_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*7 + 1, v_univApprox_2919_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2920_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*7 + 3, v_cacheInferType_2921_);
lean_inc_ref(v_t_2887_);
v___x_2927_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v___x_2924_, v_t_2887_, v___x_2926_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec_ref(v___x_2926_);
lean_dec(v___x_2924_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; size_t v_sz_2930_; size_t v___x_2931_; lean_object* v___x_2932_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref(v___x_2927_);
v___x_2929_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_sz_2930_ = lean_array_size(v_a_2928_);
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2887_, v_s_2888_, v_unificationHints_2900_, v_a_2928_, v_sz_2930_, v___x_2931_, v___x_2929_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v_a_2928_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2946_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2946_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2946_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v_fst_2937_; 
v_fst_2937_ = lean_ctor_get(v_a_2933_, 0);
lean_inc(v_fst_2937_);
lean_dec(v_a_2933_);
if (lean_obj_tag(v_fst_2937_) == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = lean_box(v___x_2903_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v___x_2938_);
v___x_2940_ = v___x_2935_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
else
{
lean_object* v_val_2942_; lean_object* v___x_2944_; 
v_val_2942_ = lean_ctor_get(v_fst_2937_, 0);
lean_inc(v_val_2942_);
lean_dec_ref(v_fst_2937_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v_val_2942_);
v___x_2944_ = v___x_2935_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_val_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
v_a_2947_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2932_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2932_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec_ref(v_s_2888_);
lean_dec_ref(v_t_2887_);
v_a_2955_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2927_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2927_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref(v_s_2888_);
lean_dec_ref(v_t_2887_);
v___x_2963_ = 0;
v___x_2964_ = lean_box(v___x_2963_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___boxed(lean_object* v_t_2986_, lean_object* v_s_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Meta_tryUnificationHints(v_t_2986_, v_s_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
return v_res_2993_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = lean_unsigned_to_nat(2674080740u);
v___x_2995_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_2996_ = l_Lean_Name_num___override(v___x_2995_, v___x_2994_);
return v___x_2996_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_2998_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_2999_ = l_Lean_Name_str___override(v___x_2998_, v___x_2997_);
return v___x_2999_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3001_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3002_ = l_Lean_Name_str___override(v___x_3001_, v___x_3000_);
return v___x_3002_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = lean_unsigned_to_nat(2u);
v___x_3004_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3005_ = l_Lean_Name_num___override(v___x_3004_, v___x_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3007_; uint8_t v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3007_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_3008_ = 0;
v___x_3009_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3010_ = l_Lean_registerTraceClass(v___x_3007_, v___x_3008_, v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
return v_res_3012_;
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
