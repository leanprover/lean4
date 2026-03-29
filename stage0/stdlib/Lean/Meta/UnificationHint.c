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
static lean_once_cell_t l_Lean_Meta_instInhabitedUnificationHints_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedUnificationHints_default___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unificationHintExtension"};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 204, 145, 124, 244, 133, 63, 146)}};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_UnificationHints_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "UnificationHint"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 112, 70, 159, 80, 199, 244, 3)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 201, 225, 55, 169, 192, 235, 23)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 76, 73, 18, 200, 34, 166, 102)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 195, 224, 136, 81, 175, 205, 78)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 1, 154, 40, 227, 230, 26, 25)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 208, 18, 32, 63, 140, 98, 77)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 91, 67, 57, 71, 246, 20, 20)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 2, 155, 161, 116, 126, 168, 23)}};
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
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
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
v___x_8_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__1(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints_default(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__1, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__1_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__1);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_instInhabitedUnificationHints_default;
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints___lam__0(lean_object* v___f_13_, lean_object* v_h_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_DiscrTree_format___redArg(v___f_13_, v_h_14_);
return v___x_15_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0));
v___x_27_ = l_Lean_Meta_Config_toConfigWithKey(v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_x_29_, lean_object* v_x_30_, lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_ks_33_; lean_object* v_vs_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_58_; 
v_ks_33_ = lean_ctor_get(v_x_29_, 0);
v_vs_34_ = lean_ctor_get(v_x_29_, 1);
v_isSharedCheck_58_ = !lean_is_exclusive(v_x_29_);
if (v_isSharedCheck_58_ == 0)
{
v___x_36_ = v_x_29_;
v_isShared_37_ = v_isSharedCheck_58_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_vs_34_);
lean_inc(v_ks_33_);
lean_dec(v_x_29_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_58_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_array_get_size(v_ks_33_);
v___x_39_ = lean_nat_dec_lt(v_x_30_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
lean_dec(v_x_30_);
v___x_40_ = lean_array_push(v_ks_33_, v_x_31_);
v___x_41_ = lean_array_push(v_vs_34_, v_x_32_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___x_41_);
lean_ctor_set(v___x_36_, 0, v___x_40_);
v___x_43_ = v___x_36_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
else
{
lean_object* v_k_x27_45_; uint8_t v___x_46_; 
v_k_x27_45_ = lean_array_fget_borrowed(v_ks_33_, v_x_30_);
v___x_46_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_31_, v_k_x27_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_48_; 
if (v_isShared_37_ == 0)
{
v___x_48_ = v___x_36_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_ks_33_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_vs_34_);
v___x_48_ = v_reuseFailAlloc_52_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_add(v_x_30_, v___x_49_);
lean_dec(v_x_30_);
v_x_29_ = v___x_48_;
v_x_30_ = v___x_50_;
goto _start;
}
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_56_; 
v___x_53_ = lean_array_fset(v_ks_33_, v_x_30_, v_x_31_);
v___x_54_ = lean_array_fset(v_vs_34_, v_x_30_, v_x_32_);
lean_dec(v_x_30_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___x_54_);
lean_ctor_set(v___x_36_, 0, v___x_53_);
v___x_56_ = v___x_36_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v___x_54_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_n_59_, lean_object* v_k_60_, lean_object* v_v_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_59_, v___x_62_, v_k_60_, v_v_61_);
return v___x_63_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_64_; size_t v___x_65_; size_t v___x_66_; 
v___x_64_ = ((size_t)5ULL);
v___x_65_ = ((size_t)1ULL);
v___x_66_ = lean_usize_shift_left(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_67_; size_t v___x_68_; size_t v___x_69_; 
v___x_67_ = ((size_t)1ULL);
v___x_68_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_69_ = lean_usize_sub(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(lean_object* v_x_71_, size_t v_x_72_, size_t v_x_73_, lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
lean_object* v_es_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; size_t v___x_80_; lean_object* v_j_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_es_76_ = lean_ctor_get(v_x_71_, 0);
v___x_77_ = ((size_t)5ULL);
v___x_78_ = ((size_t)1ULL);
v___x_79_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_80_ = lean_usize_land(v_x_72_, v___x_79_);
v_j_81_ = lean_usize_to_nat(v___x_80_);
v___x_82_ = lean_array_get_size(v_es_76_);
v___x_83_ = lean_nat_dec_lt(v_j_81_, v___x_82_);
if (v___x_83_ == 0)
{
lean_dec(v_j_81_);
lean_dec(v_x_75_);
lean_dec(v_x_74_);
return v_x_71_;
}
else
{
lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_120_; 
lean_inc_ref(v_es_76_);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v_x_71_, 0);
lean_dec(v_unused_121_);
v___x_85_ = v_x_71_;
v_isShared_86_ = v_isSharedCheck_120_;
goto v_resetjp_84_;
}
else
{
lean_dec(v_x_71_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_120_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v_v_87_; lean_object* v___x_88_; lean_object* v_xs_x27_89_; lean_object* v___y_91_; 
v_v_87_ = lean_array_fget(v_es_76_, v_j_81_);
v___x_88_ = lean_box(0);
v_xs_x27_89_ = lean_array_fset(v_es_76_, v_j_81_, v___x_88_);
switch(lean_obj_tag(v_v_87_))
{
case 0:
{
lean_object* v_key_96_; lean_object* v_val_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_107_; 
v_key_96_ = lean_ctor_get(v_v_87_, 0);
v_val_97_ = lean_ctor_get(v_v_87_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_v_87_);
if (v_isSharedCheck_107_ == 0)
{
v___x_99_ = v_v_87_;
v_isShared_100_ = v_isSharedCheck_107_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_val_97_);
lean_inc(v_key_96_);
lean_dec(v_v_87_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_107_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
uint8_t v___x_101_; 
v___x_101_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_74_, v_key_96_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_del_object(v___x_99_);
v___x_102_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_96_, v_val_97_, v_x_74_, v_x_75_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
v___y_91_ = v___x_103_;
goto v___jp_90_;
}
else
{
lean_object* v___x_105_; 
lean_dec(v_val_97_);
lean_dec(v_key_96_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v_x_75_);
lean_ctor_set(v___x_99_, 0, v_x_74_);
v___x_105_ = v___x_99_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_x_74_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_x_75_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
v___y_91_ = v___x_105_;
goto v___jp_90_;
}
}
}
}
case 1:
{
lean_object* v_node_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_118_; 
v_node_108_ = lean_ctor_get(v_v_87_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_v_87_);
if (v_isSharedCheck_118_ == 0)
{
v___x_110_ = v_v_87_;
v_isShared_111_ = v_isSharedCheck_118_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_node_108_);
lean_dec(v_v_87_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_118_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
size_t v___x_112_; size_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_112_ = lean_usize_shift_right(v_x_72_, v___x_77_);
v___x_113_ = lean_usize_add(v_x_73_, v___x_78_);
v___x_114_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_node_108_, v___x_112_, v___x_113_, v_x_74_, v_x_75_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_114_);
v___x_116_ = v___x_110_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
v___y_91_ = v___x_116_;
goto v___jp_90_;
}
}
}
default: 
{
lean_object* v___x_119_; 
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_x_74_);
lean_ctor_set(v___x_119_, 1, v_x_75_);
v___y_91_ = v___x_119_;
goto v___jp_90_;
}
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = lean_array_fset(v_xs_x27_89_, v_j_81_, v___y_91_);
lean_dec(v_j_81_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_92_);
v___x_94_ = v___x_85_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
else
{
lean_object* v_ks_122_; lean_object* v_vs_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_143_; 
v_ks_122_ = lean_ctor_get(v_x_71_, 0);
v_vs_123_ = lean_ctor_get(v_x_71_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_143_ == 0)
{
v___x_125_ = v_x_71_;
v_isShared_126_ = v_isSharedCheck_143_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_vs_123_);
lean_inc(v_ks_122_);
lean_dec(v_x_71_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_143_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_ks_122_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_vs_123_);
v___x_128_ = v_reuseFailAlloc_142_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v_newNode_129_; uint8_t v___y_131_; size_t v___x_137_; uint8_t v___x_138_; 
v_newNode_129_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(v___x_128_, v_x_74_, v_x_75_);
v___x_137_ = ((size_t)7ULL);
v___x_138_ = lean_usize_dec_le(v___x_137_, v_x_73_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_129_);
v___x_140_ = lean_unsigned_to_nat(4u);
v___x_141_ = lean_nat_dec_lt(v___x_139_, v___x_140_);
lean_dec(v___x_139_);
v___y_131_ = v___x_141_;
goto v___jp_130_;
}
else
{
v___y_131_ = v___x_138_;
goto v___jp_130_;
}
v___jp_130_:
{
if (v___y_131_ == 0)
{
lean_object* v_ks_132_; lean_object* v_vs_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_ks_132_ = lean_ctor_get(v_newNode_129_, 0);
lean_inc_ref(v_ks_132_);
v_vs_133_ = lean_ctor_get(v_newNode_129_, 1);
lean_inc_ref(v_vs_133_);
lean_dec_ref(v_newNode_129_);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2);
v___x_136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_x_73_, v_ks_132_, v_vs_133_, v___x_134_, v___x_135_);
lean_dec_ref(v_vs_133_);
lean_dec_ref(v_ks_132_);
return v___x_136_;
}
else
{
return v_newNode_129_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(size_t v_depth_144_, lean_object* v_keys_145_, lean_object* v_vals_146_, lean_object* v_i_147_, lean_object* v_entries_148_){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_array_get_size(v_keys_145_);
v___x_150_ = lean_nat_dec_lt(v_i_147_, v___x_149_);
if (v___x_150_ == 0)
{
lean_dec(v_i_147_);
return v_entries_148_;
}
else
{
lean_object* v_k_151_; lean_object* v_v_152_; uint64_t v___x_153_; size_t v_h_154_; size_t v___x_155_; lean_object* v___x_156_; size_t v___x_157_; size_t v___x_158_; size_t v___x_159_; size_t v_h_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_k_151_ = lean_array_fget_borrowed(v_keys_145_, v_i_147_);
v_v_152_ = lean_array_fget_borrowed(v_vals_146_, v_i_147_);
v___x_153_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_151_);
v_h_154_ = lean_uint64_to_usize(v___x_153_);
v___x_155_ = ((size_t)5ULL);
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_sub(v_depth_144_, v___x_157_);
v___x_159_ = lean_usize_mul(v___x_155_, v___x_158_);
v_h_160_ = lean_usize_shift_right(v_h_154_, v___x_159_);
v___x_161_ = lean_nat_add(v_i_147_, v___x_156_);
lean_dec(v_i_147_);
lean_inc(v_v_152_);
lean_inc(v_k_151_);
v___x_162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_entries_148_, v_h_160_, v_depth_144_, v_k_151_, v_v_152_);
v_i_147_ = v___x_161_;
v_entries_148_ = v___x_162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_164_, lean_object* v_keys_165_, lean_object* v_vals_166_, lean_object* v_i_167_, lean_object* v_entries_168_){
_start:
{
size_t v_depth_boxed_169_; lean_object* v_res_170_; 
v_depth_boxed_169_ = lean_unbox_usize(v_depth_164_);
lean_dec(v_depth_164_);
v_res_170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_169_, v_keys_165_, v_vals_166_, v_i_167_, v_entries_168_);
lean_dec_ref(v_vals_166_);
lean_dec_ref(v_keys_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
size_t v_x_1605__boxed_176_; size_t v_x_1606__boxed_177_; lean_object* v_res_178_; 
v_x_1605__boxed_176_ = lean_unbox_usize(v_x_172_);
lean_dec(v_x_172_);
v_x_1606__boxed_177_ = lean_unbox_usize(v_x_173_);
lean_dec(v_x_173_);
v_res_178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_171_, v_x_1605__boxed_176_, v_x_1606__boxed_177_, v_x_174_, v_x_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(lean_object* v_x_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
uint64_t v___x_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v___x_185_; 
v___x_182_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_180_);
v___x_183_ = lean_uint64_to_usize(v___x_182_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_179_, v___x_183_, v___x_184_, v_x_180_, v_x_181_);
return v___x_185_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(lean_object* v_a_186_, lean_object* v_b_187_){
_start:
{
lean_object* v_fst_188_; lean_object* v_fst_189_; uint8_t v___x_190_; 
v_fst_188_ = lean_ctor_get(v_a_186_, 0);
v_fst_189_ = lean_ctor_get(v_b_187_, 0);
v___x_190_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_188_, v_fst_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_a_191_, v_b_192_);
lean_dec_ref(v_b_192_);
lean_dec_ref(v_a_191_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(lean_object* v_x_195_, lean_object* v_keys_196_, lean_object* v_v_197_, lean_object* v_k_198_, lean_object* v_x_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_c_202_; lean_object* v___x_203_; 
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_add(v_x_195_, v___x_200_);
v_c_202_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_196_, v_v_197_, v___x_201_);
lean_dec(v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_k_198_);
lean_ctor_set(v___x_203_, 1, v_c_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_204_, lean_object* v_keys_205_, lean_object* v_v_206_, lean_object* v_k_207_, lean_object* v_x_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_204_, v_keys_205_, v_v_206_, v_k_207_, v_x_208_);
lean_dec_ref(v_keys_205_);
lean_dec(v_x_204_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5_spec__10(lean_object* v_vs_210_, lean_object* v_v_211_, lean_object* v_i_212_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_array_get_size(v_vs_210_);
v___x_214_ = lean_nat_dec_lt(v_i_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
lean_dec(v_i_212_);
v___x_215_ = lean_array_push(v_vs_210_, v_v_211_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_array_fget_borrowed(v_vs_210_, v_i_212_);
v___x_217_ = lean_name_eq(v_v_211_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_i_212_, v___x_218_);
lean_dec(v_i_212_);
v_i_212_ = v___x_219_;
goto _start;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = lean_array_fset(v_vs_210_, v_i_212_, v_v_211_);
lean_dec(v_i_212_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5(lean_object* v_vs_222_, lean_object* v_v_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5_spec__10(v_vs_222_, v_v_223_, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(lean_object* v_x_230_, lean_object* v_keys_231_, lean_object* v_v_232_, lean_object* v_k_233_, lean_object* v_as_234_, lean_object* v_k_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_mid_240_; lean_object* v_midVal_241_; uint8_t v___x_242_; 
v___x_238_ = lean_nat_add(v_x_236_, v_x_237_);
v___x_239_ = lean_unsigned_to_nat(1u);
v_mid_240_ = lean_nat_shiftr(v___x_238_, v___x_239_);
lean_dec(v___x_238_);
v_midVal_241_ = lean_array_fget(v_as_234_, v_mid_240_);
v___x_242_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_midVal_241_, v_k_235_);
if (v___x_242_ == 0)
{
uint8_t v___x_243_; 
lean_dec(v_x_237_);
v___x_243_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_k_235_, v_midVal_241_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; uint8_t v___x_245_; 
lean_dec(v_x_236_);
v___x_244_ = lean_array_get_size(v_as_234_);
v___x_245_ = lean_nat_dec_lt(v_mid_240_, v___x_244_);
if (v___x_245_ == 0)
{
lean_dec(v_midVal_241_);
lean_dec(v_mid_240_);
lean_dec(v_k_233_);
lean_dec(v_v_232_);
return v_as_234_;
}
else
{
lean_object* v_snd_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_258_; 
v_snd_246_ = lean_ctor_get(v_midVal_241_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_midVal_241_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v_midVal_241_, 0);
lean_dec(v_unused_259_);
v___x_248_ = v_midVal_241_;
v_isShared_249_ = v_isSharedCheck_258_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_snd_246_);
lean_dec(v_midVal_241_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_258_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v_xs_x27_251_; lean_object* v___x_252_; lean_object* v_c_253_; lean_object* v___x_255_; 
v___x_250_ = lean_box(0);
v_xs_x27_251_ = lean_array_fset(v_as_234_, v_mid_240_, v___x_250_);
v___x_252_ = lean_nat_add(v_x_230_, v___x_239_);
v_c_253_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_231_, v_v_232_, v___x_252_, v_snd_246_);
lean_dec(v___x_252_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_c_253_);
lean_ctor_set(v___x_248_, 0, v_k_233_);
v___x_255_ = v___x_248_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_k_233_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_c_253_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = lean_array_fset(v_xs_x27_251_, v_mid_240_, v___x_255_);
lean_dec(v_mid_240_);
return v___x_256_;
}
}
}
}
else
{
lean_dec(v_midVal_241_);
v_x_237_ = v_mid_240_;
goto _start;
}
}
else
{
uint8_t v___x_261_; 
lean_dec(v_midVal_241_);
v___x_261_ = lean_nat_dec_eq(v_mid_240_, v_x_236_);
if (v___x_261_ == 0)
{
lean_dec(v_x_236_);
v_x_236_ = v_mid_240_;
goto _start;
}
else
{
lean_object* v___x_263_; lean_object* v_c_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_j_267_; lean_object* v_as_268_; lean_object* v___x_269_; 
lean_dec(v_mid_240_);
lean_dec(v_x_237_);
v___x_263_ = lean_nat_add(v_x_230_, v___x_239_);
v_c_264_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_231_, v_v_232_, v___x_263_);
lean_dec(v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v_k_233_);
lean_ctor_set(v___x_265_, 1, v_c_264_);
v___x_266_ = lean_nat_add(v_x_236_, v___x_239_);
lean_dec(v_x_236_);
v_j_267_ = lean_array_get_size(v_as_234_);
v_as_268_ = lean_array_push(v_as_234_, v___x_265_);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_266_, v_as_268_, v_j_267_);
lean_dec(v___x_266_);
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(lean_object* v_x_270_, lean_object* v_keys_271_, lean_object* v_v_272_, lean_object* v_k_273_, lean_object* v_as_274_, lean_object* v_k_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = lean_array_get_size(v_as_274_);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_nat_dec_eq(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_array_fget_borrowed(v_as_274_, v___x_277_);
v___x_280_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_k_275_, v___x_279_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; 
v___x_281_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v___x_279_, v_k_275_);
if (v___x_281_ == 0)
{
uint8_t v___x_282_; 
v___x_282_ = lean_nat_dec_lt(v___x_277_, v___x_276_);
if (v___x_282_ == 0)
{
lean_dec(v_k_273_);
lean_dec(v_v_272_);
return v_as_274_;
}
else
{
lean_object* v___x_283_; lean_object* v_xs_x27_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_inc(v___x_279_);
v___x_283_ = lean_box(0);
v_xs_x27_284_ = lean_array_fset(v_as_274_, v___x_277_, v___x_283_);
v___x_285_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(v_x_270_, v_keys_271_, v_v_272_, v_k_273_, v___x_279_);
v___x_286_ = lean_array_fset(v_xs_x27_284_, v___x_277_, v___x_285_);
return v___x_286_;
}
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_sub(v___x_276_, v___x_287_);
v___x_289_ = lean_array_fget_borrowed(v_as_274_, v___x_288_);
v___x_290_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v___x_289_, v_k_275_);
if (v___x_290_ == 0)
{
uint8_t v___x_291_; 
v___x_291_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_k_275_, v___x_289_);
if (v___x_291_ == 0)
{
uint8_t v___x_292_; 
v___x_292_ = lean_nat_dec_lt(v___x_288_, v___x_276_);
if (v___x_292_ == 0)
{
lean_dec(v___x_288_);
lean_dec(v_k_273_);
lean_dec(v_v_272_);
return v_as_274_;
}
else
{
lean_object* v___x_293_; lean_object* v_xs_x27_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_inc(v___x_289_);
v___x_293_ = lean_box(0);
v_xs_x27_294_ = lean_array_fset(v_as_274_, v___x_288_, v___x_293_);
v___x_295_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(v_x_270_, v_keys_271_, v_v_272_, v_k_273_, v___x_289_);
v___x_296_ = lean_array_fset(v_xs_x27_294_, v___x_288_, v___x_295_);
lean_dec(v___x_288_);
return v___x_296_;
}
}
else
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_270_, v_keys_271_, v_v_272_, v_k_273_, v_as_274_, v_k_275_, v___x_277_, v___x_288_);
return v___x_297_;
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v___x_288_);
v___x_298_ = lean_box(0);
v___x_299_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_270_, v_keys_271_, v_v_272_, v_k_273_, v___x_298_);
v___x_300_ = lean_array_push(v_as_274_, v___x_299_);
return v___x_300_;
}
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_as_303_; lean_object* v___x_304_; 
v___x_301_ = lean_box(0);
v___x_302_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_270_, v_keys_271_, v_v_272_, v_k_273_, v___x_301_);
v_as_303_ = lean_array_push(v_as_274_, v___x_302_);
v___x_304_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_277_, v_as_303_, v___x_276_);
return v___x_304_;
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_box(0);
v___x_306_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_270_, v_keys_271_, v_v_272_, v_k_273_, v___x_305_);
v___x_307_ = lean_array_push(v_as_274_, v___x_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(lean_object* v_keys_308_, lean_object* v_v_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
lean_object* v_vs_312_; lean_object* v_children_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_330_; 
v_vs_312_ = lean_ctor_get(v_x_311_, 0);
v_children_313_ = lean_ctor_get(v_x_311_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_311_);
if (v_isSharedCheck_330_ == 0)
{
v___x_315_ = v_x_311_;
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_children_313_);
lean_inc(v_vs_312_);
lean_dec(v_x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_array_get_size(v_keys_308_);
v___x_318_ = lean_nat_dec_lt(v_x_310_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5(v_vs_312_, v_v_309_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_319_);
v___x_321_ = v___x_315_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_children_313_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
lean_object* v_k_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_c_326_; lean_object* v___x_328_; 
v_k_323_ = lean_array_fget_borrowed(v_keys_308_, v_x_310_);
v___x_324_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__1));
lean_inc_n(v_k_323_, 2);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_k_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v_c_326_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(v_x_310_, v_keys_308_, v_v_309_, v_k_323_, v_children_313_, v___x_325_);
lean_dec_ref(v___x_325_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v_c_326_);
v___x_328_ = v___x_315_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_vs_312_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_c_326_);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(lean_object* v_x_331_, lean_object* v_keys_332_, lean_object* v_v_333_, lean_object* v_k_334_, lean_object* v_x_335_){
_start:
{
lean_object* v_snd_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_346_; 
v_snd_336_ = lean_ctor_get(v_x_335_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; 
v_unused_347_ = lean_ctor_get(v_x_335_, 0);
lean_dec(v_unused_347_);
v___x_338_ = v_x_335_;
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_snd_336_);
lean_dec(v_x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_c_342_; lean_object* v___x_344_; 
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_x_331_, v___x_340_);
v_c_342_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_332_, v_v_333_, v___x_341_, v_snd_336_);
lean_dec(v___x_341_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v_c_342_);
lean_ctor_set(v___x_338_, 0, v_k_334_);
v___x_344_ = v___x_338_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_k_334_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_c_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_348_, lean_object* v_keys_349_, lean_object* v_v_350_, lean_object* v_k_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(v_x_348_, v_keys_349_, v_v_350_, v_k_351_, v_x_352_);
lean_dec_ref(v_keys_349_);
lean_dec(v_x_348_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___boxed(lean_object* v_keys_354_, lean_object* v_v_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_354_, v_v_355_, v_x_356_, v_x_357_);
lean_dec(v_x_356_);
lean_dec_ref(v_keys_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_x_359_, lean_object* v_keys_360_, lean_object* v_v_361_, lean_object* v_k_362_, lean_object* v_as_363_, lean_object* v_k_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v_as_363_, v_k_364_, v_x_365_, v_x_366_);
lean_dec_ref(v_k_364_);
lean_dec_ref(v_keys_360_);
lean_dec(v_x_359_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___boxed(lean_object* v_x_368_, lean_object* v_keys_369_, lean_object* v_v_370_, lean_object* v_k_371_, lean_object* v_as_372_, lean_object* v_k_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(v_x_368_, v_keys_369_, v_v_370_, v_k_371_, v_as_372_, v_k_373_);
lean_dec_ref(v_k_373_);
lean_dec_ref(v_keys_369_);
lean_dec(v_x_368_);
return v_res_374_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3(lean_object* v_msg_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0);
v___x_378_ = lean_panic_fn_borrowed(v___x_377_, v_msg_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_379_, lean_object* v_vals_380_, lean_object* v_i_381_, lean_object* v_k_382_){
_start:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_array_get_size(v_keys_379_);
v___x_384_ = lean_nat_dec_lt(v_i_381_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec(v_i_381_);
v___x_385_ = lean_box(0);
return v___x_385_;
}
else
{
lean_object* v_k_x27_386_; uint8_t v___x_387_; 
v_k_x27_386_ = lean_array_fget_borrowed(v_keys_379_, v_i_381_);
v___x_387_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_382_, v_k_x27_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_nat_add(v_i_381_, v___x_388_);
lean_dec(v_i_381_);
v_i_381_ = v___x_389_;
goto _start;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_array_fget_borrowed(v_vals_380_, v_i_381_);
lean_dec(v_i_381_);
lean_inc(v___x_391_);
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_393_, lean_object* v_vals_394_, lean_object* v_i_395_, lean_object* v_k_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_393_, v_vals_394_, v_i_395_, v_k_396_);
lean_dec(v_k_396_);
lean_dec_ref(v_vals_394_);
lean_dec_ref(v_keys_393_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(lean_object* v_x_398_, size_t v_x_399_, lean_object* v_x_400_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v_es_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_422_; 
v_es_401_ = lean_ctor_get(v_x_398_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_422_ == 0)
{
v___x_403_ = v_x_398_;
v_isShared_404_ = v_isSharedCheck_422_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_es_401_);
lean_dec(v_x_398_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_422_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; lean_object* v_j_409_; lean_object* v___x_410_; 
v___x_405_ = lean_box(2);
v___x_406_ = ((size_t)5ULL);
v___x_407_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_408_ = lean_usize_land(v_x_399_, v___x_407_);
v_j_409_ = lean_usize_to_nat(v___x_408_);
v___x_410_ = lean_array_get(v___x_405_, v_es_401_, v_j_409_);
lean_dec(v_j_409_);
lean_dec_ref(v_es_401_);
switch(lean_obj_tag(v___x_410_))
{
case 0:
{
lean_object* v_key_411_; lean_object* v_val_412_; uint8_t v___x_413_; 
v_key_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_key_411_);
v_val_412_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_val_412_);
lean_dec_ref(v___x_410_);
v___x_413_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_400_, v_key_411_);
lean_dec(v_key_411_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_dec(v_val_412_);
lean_del_object(v___x_403_);
v___x_414_ = lean_box(0);
return v___x_414_;
}
else
{
lean_object* v___x_416_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 1);
lean_ctor_set(v___x_403_, 0, v_val_412_);
v___x_416_ = v___x_403_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_val_412_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
case 1:
{
lean_object* v_node_418_; size_t v___x_419_; 
lean_del_object(v___x_403_);
v_node_418_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_node_418_);
lean_dec_ref(v___x_410_);
v___x_419_ = lean_usize_shift_right(v_x_399_, v___x_406_);
v_x_398_ = v_node_418_;
v_x_399_ = v___x_419_;
goto _start;
}
default: 
{
lean_object* v___x_421_; 
lean_del_object(v___x_403_);
v___x_421_ = lean_box(0);
return v___x_421_;
}
}
}
}
else
{
lean_object* v_ks_423_; lean_object* v_vs_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_ks_423_ = lean_ctor_get(v_x_398_, 0);
lean_inc_ref(v_ks_423_);
v_vs_424_ = lean_ctor_get(v_x_398_, 1);
lean_inc_ref(v_vs_424_);
lean_dec_ref(v_x_398_);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_423_, v_vs_424_, v___x_425_, v_x_400_);
lean_dec_ref(v_vs_424_);
lean_dec_ref(v_ks_423_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
size_t v_x_2052__boxed_430_; lean_object* v_res_431_; 
v_x_2052__boxed_430_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_431_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_427_, v_x_2052__boxed_430_, v_x_429_);
lean_dec(v_x_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint64_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_433_);
v___x_435_ = lean_uint64_to_usize(v___x_434_);
v___x_436_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_432_, v___x_435_, v_x_433_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg___boxed(lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_x_437_, v_x_438_);
lean_dec(v_x_438_);
return v_res_439_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_443_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2));
v___x_444_ = lean_unsigned_to_nat(23u);
v___x_445_ = lean_unsigned_to_nat(166u);
v___x_446_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1));
v___x_447_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0));
v___x_448_ = l_mkPanicMessageWithDecl(v___x_447_, v___x_446_, v___x_445_, v___x_444_, v___x_443_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(lean_object* v_d_449_, lean_object* v_keys_450_, lean_object* v_v_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_452_ = lean_array_get_size(v_keys_450_);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_nat_dec_eq(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v_k_456_; lean_object* v___x_457_; 
v___x_455_ = lean_box(0);
v_k_456_ = lean_array_get_borrowed(v___x_455_, v_keys_450_, v___x_453_);
lean_inc_ref(v_d_449_);
v___x_457_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_d_449_, v_k_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v___x_458_; lean_object* v_c_459_; lean_object* v___x_460_; 
v___x_458_ = lean_unsigned_to_nat(1u);
v_c_459_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_450_, v_v_451_, v___x_458_);
lean_inc(v_k_456_);
v___x_460_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_d_449_, v_k_456_, v_c_459_);
return v___x_460_;
}
else
{
lean_object* v_val_461_; lean_object* v___x_462_; lean_object* v_c_463_; lean_object* v___x_464_; 
v_val_461_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_val_461_);
lean_dec_ref(v___x_457_);
v___x_462_ = lean_unsigned_to_nat(1u);
v_c_463_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_450_, v_v_451_, v___x_462_, v_val_461_);
lean_inc(v_k_456_);
v___x_464_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_d_449_, v_k_456_, v_c_463_);
return v___x_464_;
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v_v_451_);
lean_dec_ref(v_d_449_);
v___x_465_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3);
v___x_466_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3(v___x_465_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___boxed(lean_object* v_d_467_, lean_object* v_keys_468_, lean_object* v_v_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_d_467_, v_keys_468_, v_v_469_);
lean_dec_ref(v_keys_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* v_hints_471_, lean_object* v_e_472_){
_start:
{
lean_object* v_keys_473_; lean_object* v_val_474_; lean_object* v___x_475_; 
v_keys_473_ = lean_ctor_get(v_e_472_, 0);
lean_inc_ref(v_keys_473_);
v_val_474_ = lean_ctor_get(v_e_472_, 1);
lean_inc(v_val_474_);
lean_dec_ref(v_e_472_);
v___x_475_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_hints_471_, v_keys_473_, v_val_474_);
lean_dec_ref(v_keys_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_x_477_, v_x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_00_u03b2_480_, v_x_481_, v_x_482_);
lean_dec(v_x_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(lean_object* v_00_u03b2_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_x_485_, v_x_486_, v_x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_489_, lean_object* v_x_490_, size_t v_x_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_490_, v_x_491_, v_x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_494_, lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
size_t v_x_2194__boxed_498_; lean_object* v_res_499_; 
v_x_2194__boxed_498_ = lean_unbox_usize(v_x_496_);
lean_dec(v_x_496_);
v_res_499_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(v_00_u03b2_494_, v_x_495_, v_x_2194__boxed_498_, v_x_497_);
lean_dec(v_x_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_500_, lean_object* v_x_501_, size_t v_x_502_, size_t v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_501_, v_x_502_, v_x_503_, v_x_504_, v_x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_507_, lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
size_t v_x_2205__boxed_513_; size_t v_x_2206__boxed_514_; lean_object* v_res_515_; 
v_x_2205__boxed_513_ = lean_unbox_usize(v_x_509_);
lean_dec(v_x_509_);
v_x_2206__boxed_514_ = lean_unbox_usize(v_x_510_);
lean_dec(v_x_510_);
v_res_515_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3(v_00_u03b2_507_, v_x_508_, v_x_2205__boxed_513_, v_x_2206__boxed_514_, v_x_511_, v_x_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_516_, lean_object* v_keys_517_, lean_object* v_vals_518_, lean_object* v_heq_519_, lean_object* v_i_520_, lean_object* v_k_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_517_, v_vals_518_, v_i_520_, v_k_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_523_, lean_object* v_keys_524_, lean_object* v_vals_525_, lean_object* v_heq_526_, lean_object* v_i_527_, lean_object* v_k_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_523_, v_keys_524_, v_vals_525_, v_heq_526_, v_i_527_, v_k_528_);
lean_dec(v_k_528_);
lean_dec_ref(v_vals_525_);
lean_dec_ref(v_keys_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_530_, lean_object* v_n_531_, lean_object* v_k_532_, lean_object* v_v_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(v_n_531_, v_k_532_, v_v_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_535_, size_t v_depth_536_, lean_object* v_keys_537_, lean_object* v_vals_538_, lean_object* v_heq_539_, lean_object* v_i_540_, lean_object* v_entries_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_536_, v_keys_537_, v_vals_538_, v_i_540_, v_entries_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_543_, lean_object* v_depth_544_, lean_object* v_keys_545_, lean_object* v_vals_546_, lean_object* v_heq_547_, lean_object* v_i_548_, lean_object* v_entries_549_){
_start:
{
size_t v_depth_boxed_550_; lean_object* v_res_551_; 
v_depth_boxed_550_ = lean_unbox_usize(v_depth_544_);
lean_dec(v_depth_544_);
v_res_551_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_543_, v_depth_boxed_550_, v_keys_545_, v_vals_546_, v_heq_547_, v_i_548_, v_entries_549_);
lean_dec_ref(v_vals_546_);
lean_dec_ref(v_keys_545_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12(lean_object* v_x_552_, lean_object* v_keys_553_, lean_object* v_v_554_, lean_object* v_k_555_, lean_object* v_as_556_, lean_object* v_k_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_552_, v_keys_553_, v_v_554_, v_k_555_, v_as_556_, v_k_557_, v_x_558_, v_x_559_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_x_563_, lean_object* v_keys_564_, lean_object* v_v_565_, lean_object* v_k_566_, lean_object* v_as_567_, lean_object* v_k_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12(v_x_563_, v_keys_564_, v_v_565_, v_k_566_, v_as_567_, v_k_568_, v_x_569_, v_x_570_, v_x_571_, v_x_572_);
lean_dec_ref(v_k_568_);
lean_dec_ref(v_keys_564_);
lean_dec(v_x_563_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_575_, v_x_576_, v_x_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(uint8_t v_x_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___y_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_x_583_, lean_object* v___y_584_){
_start:
{
uint8_t v_x_26__boxed_585_; lean_object* v_res_586_; 
v_x_26__boxed_585_ = lean_unbox(v_x_583_);
v_res_586_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v_x_26__boxed_585_, v___y_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object* v___y_587_){
_start:
{
lean_inc_ref(v___y_587_);
return v___y_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v___y_588_);
lean_dec_ref(v___y_588_);
return v_res_589_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_600_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___f_601_ = ((lean_object*)(l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___f_602_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_603_ = lean_obj_once(&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_);
v___x_604_ = ((lean_object*)(l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_605_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
lean_ctor_set(v___x_606_, 2, v___x_603_);
lean_ctor_set(v___x_606_, 3, v___f_602_);
lean_ctor_set(v___x_606_, 4, v___f_601_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_);
v___x_609_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
return v_res_611_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2));
v___x_617_ = l_Lean_stringToMessageData(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object* v_e_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_619_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1));
v___x_620_ = lean_unsigned_to_nat(3u);
v___x_621_ = l_Lean_Expr_isAppOfArity(v_e_618_, v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3);
v___x_623_ = l_Lean_indentExpr(v_e_618_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_626_ = l_Lean_Expr_appFn_x21(v_e_618_);
v___x_627_ = l_Lean_Expr_appArg_x21(v___x_626_);
lean_dec_ref(v___x_626_);
v___x_628_ = l_Lean_Expr_appArg_x21(v_e_618_);
lean_dec_ref(v_e_618_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0));
v___x_633_ = l_Lean_stringToMessageData(v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object* v_e_634_, lean_object* v_cs_635_){
_start:
{
if (lean_obj_tag(v_e_634_) == 7)
{
lean_object* v_binderType_636_; lean_object* v_body_637_; lean_object* v___x_638_; 
v_binderType_636_ = lean_ctor_get(v_e_634_, 1);
v_body_637_ = lean_ctor_get(v_e_634_, 2);
lean_inc_ref(v_binderType_636_);
v___x_638_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_binderType_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_e_634_);
lean_dec_ref(v_cs_635_);
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_660_; 
v_a_647_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_660_ == 0)
{
v___x_649_ = v___x_638_;
v_isShared_650_ = v_isSharedCheck_660_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_638_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_660_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
uint8_t v___x_651_; 
v___x_651_ = l_Lean_Expr_hasLooseBVars(v_body_637_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_inc_ref(v_body_637_);
lean_del_object(v___x_649_);
lean_dec_ref(v_e_634_);
v___x_652_ = lean_array_push(v_cs_635_, v_a_647_);
v_e_634_ = v_body_637_;
v_cs_635_ = v___x_652_;
goto _start;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
lean_dec(v_a_647_);
lean_dec_ref(v_cs_635_);
v___x_654_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1);
v___x_655_ = l_Lean_indentExpr(v_e_634_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 0);
lean_ctor_set(v___x_649_, 0, v___x_656_);
v___x_658_ = v___x_649_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
else
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_e_634_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_cs_635_);
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_679_; 
v_a_670_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_679_ == 0)
{
v___x_672_ = v___x_661_;
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_661_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_674_ = lean_array_to_list(v_cs_635_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_a_670_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_675_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object* v_e_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0));
v___x_684_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(v_e_682_, v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(lean_object* v_msgData_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v_env_692_; lean_object* v___x_693_; lean_object* v_mctx_694_; lean_object* v_lctx_695_; lean_object* v_options_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_691_ = lean_st_ref_get(v___y_689_);
v_env_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref(v_env_692_);
lean_dec(v___x_691_);
v___x_693_ = lean_st_ref_get(v___y_687_);
v_mctx_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_mctx_694_);
lean_dec(v___x_693_);
v_lctx_695_ = lean_ctor_get(v___y_686_, 2);
v_options_696_ = lean_ctor_get(v___y_688_, 2);
lean_inc_ref(v_options_696_);
lean_inc_ref(v_lctx_695_);
v___x_697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_697_, 0, v_env_692_);
lean_ctor_set(v___x_697_, 1, v_mctx_694_);
lean_ctor_set(v___x_697_, 2, v_lctx_695_);
lean_ctor_set(v___x_697_, 3, v_options_696_);
v___x_698_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_msgData_685_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object* v_msgData_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msgData_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(lean_object* v_msg_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_ref_713_; lean_object* v___x_714_; lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
v_ref_713_ = lean_ctor_get(v___y_710_, 5);
v___x_714_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_723_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
lean_inc(v_ref_713_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v_ref_713_);
lean_ctor_set(v___x_719_, 1, v_a_715_);
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 1);
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg___boxed(lean_object* v_msg_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_730_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0));
v___x_733_ = l_Lean_stringToMessageData(v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2));
v___x_736_ = l_Lean_stringToMessageData(v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(lean_object* v_as_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
if (lean_obj_tag(v_as_737_) == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v_head_745_; lean_object* v_tail_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_780_; 
v_head_745_ = lean_ctor_get(v_as_737_, 0);
v_tail_746_ = lean_ctor_get(v_as_737_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_as_737_);
if (v_isSharedCheck_780_ == 0)
{
v___x_748_ = v_as_737_;
v_isShared_749_ = v_isSharedCheck_780_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_tail_746_);
lean_inc(v_head_745_);
lean_dec(v_as_737_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_780_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_lhs_750_; lean_object* v_rhs_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_779_; 
v_lhs_750_ = lean_ctor_get(v_head_745_, 0);
v_rhs_751_ = lean_ctor_get(v_head_745_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_head_745_);
if (v_isSharedCheck_779_ == 0)
{
v___x_753_ = v_head_745_;
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_rhs_751_);
lean_inc(v_lhs_750_);
lean_dec(v_head_745_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; 
lean_inc_ref(v_rhs_751_);
lean_inc_ref(v_lhs_750_);
v___x_755_ = l_Lean_Meta_isExprDefEq(v_lhs_750_, v_rhs_751_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; uint8_t v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_755_);
v___x_757_ = lean_unbox(v_a_756_);
lean_dec(v_a_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec(v_tail_746_);
v___x_758_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1);
v___x_759_ = l_Lean_indentExpr(v_lhs_750_);
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 7);
lean_ctor_set(v___x_753_, 1, v___x_759_);
lean_ctor_set(v___x_753_, 0, v___x_758_);
v___x_761_ = v___x_753_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_769_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 7);
lean_ctor_set(v___x_748_, 1, v___x_762_);
lean_ctor_set(v___x_748_, 0, v___x_761_);
v___x_764_ = v___x_748_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_762_);
v___x_764_ = v_reuseFailAlloc_768_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = l_Lean_indentExpr(v_rhs_751_);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_766_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
return v___x_767_;
}
}
}
else
{
lean_del_object(v___x_753_);
lean_dec_ref(v_rhs_751_);
lean_dec_ref(v_lhs_750_);
lean_del_object(v___x_748_);
v_as_737_ = v_tail_746_;
goto _start;
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_del_object(v___x_753_);
lean_dec_ref(v_rhs_751_);
lean_dec_ref(v_lhs_750_);
lean_del_object(v___x_748_);
lean_dec(v_tail_746_);
v_a_771_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_755_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_755_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___boxed(lean_object* v_as_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_as_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_787_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object* v_hint_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_pattern_797_; lean_object* v_constraints_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_840_; 
v_pattern_797_ = lean_ctor_get(v_hint_791_, 0);
v_constraints_798_ = lean_ctor_get(v_hint_791_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_hint_791_);
if (v_isSharedCheck_840_ == 0)
{
v___x_800_ = v_hint_791_;
v_isShared_801_ = v_isSharedCheck_840_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_constraints_798_);
lean_inc(v_pattern_797_);
lean_dec(v_hint_791_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_840_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; 
v___x_802_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_constraints_798_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_lhs_803_; lean_object* v_rhs_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref(v___x_802_);
v_lhs_803_ = lean_ctor_get(v_pattern_797_, 0);
v_rhs_804_ = lean_ctor_get(v_pattern_797_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_pattern_797_);
if (v_isSharedCheck_839_ == 0)
{
v___x_806_ = v_pattern_797_;
v_isShared_807_ = v_isSharedCheck_839_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_rhs_804_);
lean_inc(v_lhs_803_);
lean_dec(v_pattern_797_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_839_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; 
lean_inc_ref(v_rhs_804_);
lean_inc_ref(v_lhs_803_);
v___x_808_ = l_Lean_Meta_isExprDefEq(v_lhs_803_, v_rhs_804_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_830_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_830_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_830_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_830_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
uint8_t v___x_813_; 
v___x_813_ = lean_unbox(v_a_809_);
lean_dec(v_a_809_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_del_object(v___x_811_);
v___x_814_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1);
v___x_815_ = l_Lean_indentExpr(v_lhs_803_);
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 7);
lean_ctor_set(v___x_806_, 1, v___x_815_);
lean_ctor_set(v___x_806_, 0, v___x_814_);
v___x_817_ = v___x_806_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_825_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 7);
lean_ctor_set(v___x_800_, 1, v___x_818_);
lean_ctor_set(v___x_800_, 0, v___x_817_);
v___x_820_ = v___x_800_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_818_);
v___x_820_ = v_reuseFailAlloc_824_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = l_Lean_indentExpr(v_rhs_804_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_822_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_823_;
}
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_del_object(v___x_806_);
lean_dec_ref(v_rhs_804_);
lean_dec_ref(v_lhs_803_);
lean_del_object(v___x_800_);
v___x_826_ = lean_box(0);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_826_);
v___x_828_ = v___x_811_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
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
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_del_object(v___x_806_);
lean_dec_ref(v_rhs_804_);
lean_dec_ref(v_lhs_803_);
lean_del_object(v___x_800_);
v_a_831_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_808_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_808_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
else
{
lean_del_object(v___x_800_);
lean_dec_ref(v_pattern_797_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object* v_hint_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_hint_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object* v_00_u03b1_848_, lean_object* v_msg_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object* v_00_u03b1_856_, lean_object* v_msg_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(v_00_u03b1_856_, v_msg_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_863_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_864_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_870_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
lean_ctor_set(v___x_870_, 2, v___x_869_);
lean_ctor_set(v___x_870_, 3, v___x_869_);
lean_ctor_set(v___x_870_, 4, v___x_869_);
lean_ctor_set(v___x_870_, 5, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(lean_object* v_ext_871_, lean_object* v_b_872_, uint8_t v_kind_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_currNamespace_878_; lean_object* v___x_879_; lean_object* v_env_880_; lean_object* v_nextMacroScope_881_; lean_object* v_ngen_882_; lean_object* v_auxDeclNGen_883_; lean_object* v_traceState_884_; lean_object* v_messages_885_; lean_object* v_infoState_886_; lean_object* v_snapshotTasks_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_914_; 
v_currNamespace_878_ = lean_ctor_get(v___y_875_, 6);
v___x_879_ = lean_st_ref_take(v___y_876_);
v_env_880_ = lean_ctor_get(v___x_879_, 0);
v_nextMacroScope_881_ = lean_ctor_get(v___x_879_, 1);
v_ngen_882_ = lean_ctor_get(v___x_879_, 2);
v_auxDeclNGen_883_ = lean_ctor_get(v___x_879_, 3);
v_traceState_884_ = lean_ctor_get(v___x_879_, 4);
v_messages_885_ = lean_ctor_get(v___x_879_, 6);
v_infoState_886_ = lean_ctor_get(v___x_879_, 7);
v_snapshotTasks_887_ = lean_ctor_get(v___x_879_, 8);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v___x_879_, 5);
lean_dec(v_unused_915_);
v___x_889_ = v___x_879_;
v_isShared_890_ = v_isSharedCheck_914_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_snapshotTasks_887_);
lean_inc(v_infoState_886_);
lean_inc(v_messages_885_);
lean_inc(v_traceState_884_);
lean_inc(v_auxDeclNGen_883_);
lean_inc(v_ngen_882_);
lean_inc(v_nextMacroScope_881_);
lean_inc(v_env_880_);
lean_dec(v___x_879_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_914_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
lean_inc(v_currNamespace_878_);
v___x_891_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_880_, v_ext_871_, v_b_872_, v_kind_873_, v_currNamespace_878_);
v___x_892_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 5, v___x_892_);
lean_ctor_set(v___x_889_, 0, v___x_891_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_nextMacroScope_881_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_ngen_882_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_auxDeclNGen_883_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_traceState_884_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_913_, 6, v_messages_885_);
lean_ctor_set(v_reuseFailAlloc_913_, 7, v_infoState_886_);
lean_ctor_set(v_reuseFailAlloc_913_, 8, v_snapshotTasks_887_);
v___x_894_ = v_reuseFailAlloc_913_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_mctx_897_; lean_object* v_zetaDeltaFVarIds_898_; lean_object* v_postponed_899_; lean_object* v_diag_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_911_; 
v___x_895_ = lean_st_ref_set(v___y_876_, v___x_894_);
v___x_896_ = lean_st_ref_take(v___y_874_);
v_mctx_897_ = lean_ctor_get(v___x_896_, 0);
v_zetaDeltaFVarIds_898_ = lean_ctor_get(v___x_896_, 2);
v_postponed_899_ = lean_ctor_get(v___x_896_, 3);
v_diag_900_ = lean_ctor_get(v___x_896_, 4);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_896_, 1);
lean_dec(v_unused_912_);
v___x_902_ = v___x_896_;
v_isShared_903_ = v_isSharedCheck_911_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_diag_900_);
lean_inc(v_postponed_899_);
lean_inc(v_zetaDeltaFVarIds_898_);
lean_inc(v_mctx_897_);
lean_dec(v___x_896_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_911_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 1, v___x_904_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_mctx_897_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_zetaDeltaFVarIds_898_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_postponed_899_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_diag_900_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_st_ref_set(v___y_874_, v___x_906_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(lean_object* v_ext_916_, lean_object* v_b_917_, lean_object* v_kind_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
uint8_t v_kind_boxed_923_; lean_object* v_res_924_; 
v_kind_boxed_923_ = lean_unbox(v_kind_918_);
v_res_924_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_916_, v_b_917_, v_kind_boxed_923_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_00_u03c3_927_, lean_object* v_ext_928_, lean_object* v_b_929_, uint8_t v_kind_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_928_, v_b_929_, v_kind_930_, v___y_932_, v___y_933_, v___y_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object* v_00_u03b1_937_, lean_object* v_00_u03b2_938_, lean_object* v_00_u03c3_939_, lean_object* v_ext_940_, lean_object* v_b_941_, lean_object* v_kind_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
uint8_t v_kind_boxed_948_; lean_object* v_res_949_; 
v_kind_boxed_948_ = lean_unbox(v_kind_942_);
v_res_949_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(v_00_u03b1_937_, v_00_u03b2_938_, v_00_u03c3_939_, v_ext_940_, v_b_941_, v_kind_boxed_948_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(lean_object* v_k_950_, uint8_t v_allowLevelAssignments_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_951_, v_k_950_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_966_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_957_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_957_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(lean_object* v_k_974_, lean_object* v_allowLevelAssignments_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_981_; lean_object* v_res_982_; 
v_allowLevelAssignments_boxed_981_ = lean_unbox(v_allowLevelAssignments_975_);
v_res_982_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_974_, v_allowLevelAssignments_boxed_981_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(lean_object* v_00_u03b1_983_, lean_object* v_k_984_, uint8_t v_allowLevelAssignments_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_984_, v_allowLevelAssignments_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(lean_object* v_00_u03b1_992_, lean_object* v_k_993_, lean_object* v_allowLevelAssignments_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1000_; lean_object* v_res_1001_; 
v_allowLevelAssignments_boxed_1000_ = lean_unbox(v_allowLevelAssignments_994_);
v_res_1001_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(v_00_u03b1_992_, v_k_993_, v_allowLevelAssignments_boxed_1000_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_ctor_set(v___x_1007_, 2, v___x_1006_);
lean_ctor_set(v___x_1007_, 3, v___x_1005_);
lean_ctor_set(v___x_1007_, 4, v___x_1005_);
lean_ctor_set(v___x_1007_, 5, v___x_1005_);
lean_ctor_set(v___x_1007_, 6, v___x_1005_);
lean_ctor_set(v___x_1007_, 7, v___x_1005_);
lean_ctor_set(v___x_1007_, 8, v___x_1005_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_unsigned_to_nat(32u);
v___x_1009_ = lean_mk_empty_array_with_capacity(v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1011_ = ((size_t)5ULL);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_unsigned_to_nat(32u);
v___x_1014_ = lean_mk_empty_array_with_capacity(v___x_1013_);
v___x_1015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1016_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_1014_);
lean_ctor_set(v___x_1016_, 2, v___x_1012_);
lean_ctor_set(v___x_1016_, 3, v___x_1012_);
lean_ctor_set_usize(v___x_1016_, 4, v___x_1011_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1017_ = lean_box(1);
v___x_1018_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1019_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1020_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_1018_);
lean_ctor_set(v___x_1020_, 2, v___x_1017_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1042_, lean_object* v_declHint_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; lean_object* v_env_1047_; uint8_t v___x_1048_; 
v___x_1046_ = lean_st_ref_get(v___y_1044_);
v_env_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc_ref(v_env_1047_);
lean_dec(v___x_1046_);
v___x_1048_ = l_Lean_Name_isAnonymous(v_declHint_1043_);
if (v___x_1048_ == 0)
{
uint8_t v_isExporting_1049_; 
v_isExporting_1049_ = lean_ctor_get_uint8(v_env_1047_, sizeof(void*)*8);
if (v_isExporting_1049_ == 0)
{
lean_object* v___x_1050_; 
lean_dec_ref(v_env_1047_);
lean_dec(v_declHint_1043_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_msg_1042_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
lean_inc_ref(v_env_1047_);
v___x_1051_ = l_Lean_Environment_setExporting(v_env_1047_, v___x_1048_);
lean_inc(v_declHint_1043_);
lean_inc_ref(v___x_1051_);
v___x_1052_ = l_Lean_Environment_contains(v___x_1051_, v_declHint_1043_, v_isExporting_1049_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec_ref(v___x_1051_);
lean_dec_ref(v_env_1047_);
lean_dec(v_declHint_1043_);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_msg_1042_);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v_c_1059_; lean_object* v___x_1060_; 
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1055_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1056_ = l_Lean_Options_empty;
v___x_1057_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1051_);
lean_ctor_set(v___x_1057_, 1, v___x_1054_);
lean_ctor_set(v___x_1057_, 2, v___x_1055_);
lean_ctor_set(v___x_1057_, 3, v___x_1056_);
lean_inc(v_declHint_1043_);
v___x_1058_ = l_Lean_MessageData_ofConstName(v_declHint_1043_, v___x_1048_);
v_c_1059_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1059_, 0, v___x_1057_);
lean_ctor_set(v_c_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1047_, v_declHint_1043_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec_ref(v_env_1047_);
lean_dec(v_declHint_1043_);
v___x_1061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_c_1059_);
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = l_Lean_MessageData_note(v___x_1064_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_msg_1042_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v_val_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1103_; 
v_val_1068_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1070_ = v___x_1060_;
v_isShared_1071_ = v_isSharedCheck_1103_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_val_1068_);
lean_dec(v___x_1060_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1103_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_mod_1075_; uint8_t v___x_1076_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = l_Lean_Environment_header(v_env_1047_);
lean_dec_ref(v_env_1047_);
v___x_1074_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1073_);
v_mod_1075_ = lean_array_get(v___x_1072_, v___x_1074_, v_val_1068_);
lean_dec(v_val_1068_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = l_Lean_isPrivateName(v_declHint_1043_);
lean_dec(v_declHint_1043_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v_c_1059_);
v___x_1079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_MessageData_ofName(v_mod_1075_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_MessageData_note(v___x_1084_);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_msg_1042_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1086_);
v___x_1088_ = v___x_1070_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1090_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_c_1059_);
v___x_1092_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_MessageData_ofName(v_mod_1075_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_MessageData_note(v___x_1097_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_msg_1042_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1099_);
v___x_1101_ = v___x_1070_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1104_; 
lean_dec_ref(v_env_1047_);
lean_dec(v_declHint_1043_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_msg_1042_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1105_, lean_object* v_declHint_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1105_, v_declHint_1106_, v___y_1107_);
lean_dec(v___y_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object* v_msg_1110_, lean_object* v_declHint_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1127_; 
v___x_1117_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1110_, v_declHint_1111_, v___y_1115_);
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1127_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1127_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1122_ = l_Lean_unknownIdentifierMessageTag;
v___x_1123_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_a_1118_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1123_);
v___x_1125_ = v___x_1120_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1128_, lean_object* v_declHint_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1128_, v_declHint_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1136_, lean_object* v_msg_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_fileName_1143_; lean_object* v_fileMap_1144_; lean_object* v_options_1145_; lean_object* v_currRecDepth_1146_; lean_object* v_maxRecDepth_1147_; lean_object* v_ref_1148_; lean_object* v_currNamespace_1149_; lean_object* v_openDecls_1150_; lean_object* v_initHeartbeats_1151_; lean_object* v_maxHeartbeats_1152_; lean_object* v_quotContext_1153_; lean_object* v_currMacroScope_1154_; uint8_t v_diag_1155_; lean_object* v_cancelTk_x3f_1156_; uint8_t v_suppressElabErrors_1157_; lean_object* v_inheritedTraceOptions_1158_; lean_object* v_ref_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_fileName_1143_ = lean_ctor_get(v___y_1140_, 0);
v_fileMap_1144_ = lean_ctor_get(v___y_1140_, 1);
v_options_1145_ = lean_ctor_get(v___y_1140_, 2);
v_currRecDepth_1146_ = lean_ctor_get(v___y_1140_, 3);
v_maxRecDepth_1147_ = lean_ctor_get(v___y_1140_, 4);
v_ref_1148_ = lean_ctor_get(v___y_1140_, 5);
v_currNamespace_1149_ = lean_ctor_get(v___y_1140_, 6);
v_openDecls_1150_ = lean_ctor_get(v___y_1140_, 7);
v_initHeartbeats_1151_ = lean_ctor_get(v___y_1140_, 8);
v_maxHeartbeats_1152_ = lean_ctor_get(v___y_1140_, 9);
v_quotContext_1153_ = lean_ctor_get(v___y_1140_, 10);
v_currMacroScope_1154_ = lean_ctor_get(v___y_1140_, 11);
v_diag_1155_ = lean_ctor_get_uint8(v___y_1140_, sizeof(void*)*14);
v_cancelTk_x3f_1156_ = lean_ctor_get(v___y_1140_, 12);
v_suppressElabErrors_1157_ = lean_ctor_get_uint8(v___y_1140_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1158_ = lean_ctor_get(v___y_1140_, 13);
v_ref_1159_ = l_Lean_replaceRef(v_ref_1136_, v_ref_1148_);
lean_inc_ref(v_inheritedTraceOptions_1158_);
lean_inc(v_cancelTk_x3f_1156_);
lean_inc(v_currMacroScope_1154_);
lean_inc(v_quotContext_1153_);
lean_inc(v_maxHeartbeats_1152_);
lean_inc(v_initHeartbeats_1151_);
lean_inc(v_openDecls_1150_);
lean_inc(v_currNamespace_1149_);
lean_inc(v_maxRecDepth_1147_);
lean_inc(v_currRecDepth_1146_);
lean_inc_ref(v_options_1145_);
lean_inc_ref(v_fileMap_1144_);
lean_inc_ref(v_fileName_1143_);
v___x_1160_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1160_, 0, v_fileName_1143_);
lean_ctor_set(v___x_1160_, 1, v_fileMap_1144_);
lean_ctor_set(v___x_1160_, 2, v_options_1145_);
lean_ctor_set(v___x_1160_, 3, v_currRecDepth_1146_);
lean_ctor_set(v___x_1160_, 4, v_maxRecDepth_1147_);
lean_ctor_set(v___x_1160_, 5, v_ref_1159_);
lean_ctor_set(v___x_1160_, 6, v_currNamespace_1149_);
lean_ctor_set(v___x_1160_, 7, v_openDecls_1150_);
lean_ctor_set(v___x_1160_, 8, v_initHeartbeats_1151_);
lean_ctor_set(v___x_1160_, 9, v_maxHeartbeats_1152_);
lean_ctor_set(v___x_1160_, 10, v_quotContext_1153_);
lean_ctor_set(v___x_1160_, 11, v_currMacroScope_1154_);
lean_ctor_set(v___x_1160_, 12, v_cancelTk_x3f_1156_);
lean_ctor_set(v___x_1160_, 13, v_inheritedTraceOptions_1158_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*14, v_diag_1155_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*14 + 1, v_suppressElabErrors_1157_);
v___x_1161_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_1137_, v___y_1138_, v___y_1139_, v___x_1160_, v___y_1141_);
lean_dec_ref(v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1162_, lean_object* v_msg_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1162_, v_msg_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v_ref_1162_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_ref_1170_, lean_object* v_msg_1171_, lean_object* v_declHint_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v_a_1179_; lean_object* v___x_1180_; 
v___x_1178_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1171_, v_declHint_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref(v___x_1178_);
v___x_1180_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1170_, v_a_1179_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1181_, lean_object* v_msg_1182_, lean_object* v_declHint_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1181_, v_msg_1182_, v_declHint_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v_ref_1181_);
return v_res_1189_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1192_ = l_Lean_stringToMessageData(v___x_1191_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1195_ = l_Lean_stringToMessageData(v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1196_, lean_object* v_constName_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1203_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1204_ = 0;
lean_inc(v_constName_1197_);
v___x_1205_ = l_Lean_MessageData_ofConstName(v_constName_1197_, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1203_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1196_, v___x_1208_, v_constName_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1210_, lean_object* v_constName_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1210_, v_constName_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v_ref_1210_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(lean_object* v_constName_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_ref_1224_; lean_object* v___x_1225_; 
v_ref_1224_ = lean_ctor_get(v___y_1221_, 5);
v___x_1225_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1224_, v_constName_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(lean_object* v_constName_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; lean_object* v_env_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = lean_st_ref_get(v___y_1237_);
v_env_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_ref(v_env_1240_);
lean_dec(v___x_1239_);
v___x_1241_ = 0;
lean_inc(v_constName_1233_);
v___x_1242_ = l_Lean_Environment_find_x3f(v_env_1240_, v_constName_1233_, v___x_1241_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1243_;
}
else
{
lean_object* v_val_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec(v_constName_1233_);
v_val_1244_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1242_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_val_1244_);
lean_dec(v___x_1242_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 0);
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_val_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(lean_object* v_constName_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_constName_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_Meta_addUnificationHint___lam__0___closed__0));
v___x_1261_ = l_Lean_stringToMessageData(v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object* v_declName_1262_, uint8_t v_kind_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
lean_inc(v_declName_1262_);
v___x_1269_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_declName_1262_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
v___x_1271_ = 0;
v___x_1272_ = l_Lean_ConstantInfo_value_x3f(v_a_1270_, v___x_1271_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec(v_declName_1262_);
v___x_1273_ = lean_obj_once(&l_Lean_Meta_addUnificationHint___lam__0___closed__1, &l_Lean_Meta_addUnificationHint___lam__0___closed__1_once, _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1);
v___x_1274_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_1273_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1274_;
}
else
{
lean_object* v_val_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_val_1275_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_val_1275_);
lean_dec_ref(v___x_1272_);
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Lean_Meta_lambdaMetaTelescope(v_val_1275_, v___x_1276_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v_val_1275_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v_snd_1279_; lean_object* v_snd_1280_; lean_object* v___x_1281_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v_snd_1279_ = lean_ctor_get(v_a_1278_, 1);
lean_inc(v_snd_1279_);
lean_dec(v_a_1278_);
v_snd_1280_ = lean_ctor_get(v_snd_1279_, 1);
lean_inc(v_snd_1280_);
lean_dec(v_snd_1279_);
v___x_1281_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_1280_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1283_; 
lean_dec(v_declName_1262_);
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_a_1282_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1283_;
}
else
{
lean_object* v_a_1284_; lean_object* v_pattern_1285_; lean_object* v_lhs_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1321_; 
v_a_1284_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1281_);
v_pattern_1285_ = lean_ctor_get(v_a_1284_, 0);
lean_inc_ref(v_pattern_1285_);
v_lhs_1286_ = lean_ctor_get(v_pattern_1285_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_pattern_1285_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v_pattern_1285_, 1);
lean_dec(v_unused_1322_);
v___x_1288_ = v_pattern_1285_;
v_isShared_1289_ = v_isSharedCheck_1321_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_lhs_1286_);
lean_dec(v_pattern_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1321_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v_config_1291_; uint8_t v_trackZetaDelta_1292_; lean_object* v_zetaDeltaSet_1293_; lean_object* v_lctx_1294_; lean_object* v_localInstances_1295_; lean_object* v_defEqCtx_x3f_1296_; lean_object* v_synthPendingDepth_1297_; lean_object* v_canUnfold_x3f_1298_; uint8_t v_univApprox_1299_; uint8_t v_inTypeClassResolution_1300_; uint8_t v_cacheInferType_1301_; uint64_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1290_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_1291_ = lean_ctor_get(v___x_1290_, 0);
v_trackZetaDelta_1292_ = lean_ctor_get_uint8(v___y_1264_, sizeof(void*)*7);
v_zetaDeltaSet_1293_ = lean_ctor_get(v___y_1264_, 1);
v_lctx_1294_ = lean_ctor_get(v___y_1264_, 2);
v_localInstances_1295_ = lean_ctor_get(v___y_1264_, 3);
v_defEqCtx_x3f_1296_ = lean_ctor_get(v___y_1264_, 4);
v_synthPendingDepth_1297_ = lean_ctor_get(v___y_1264_, 5);
v_canUnfold_x3f_1298_ = lean_ctor_get(v___y_1264_, 6);
v_univApprox_1299_ = lean_ctor_get_uint8(v___y_1264_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1300_ = lean_ctor_get_uint8(v___y_1264_, sizeof(void*)*7 + 2);
v_cacheInferType_1301_ = lean_ctor_get_uint8(v___y_1264_, sizeof(void*)*7 + 3);
v___x_1302_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1291_);
lean_inc_ref(v_config_1291_);
v___x_1303_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1303_, 0, v_config_1291_);
lean_ctor_set_uint64(v___x_1303_, sizeof(void*)*1, v___x_1302_);
lean_inc(v_canUnfold_x3f_1298_);
lean_inc(v_synthPendingDepth_1297_);
lean_inc(v_defEqCtx_x3f_1296_);
lean_inc_ref(v_localInstances_1295_);
lean_inc_ref(v_lctx_1294_);
lean_inc(v_zetaDeltaSet_1293_);
v___x_1304_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v_zetaDeltaSet_1293_);
lean_ctor_set(v___x_1304_, 2, v_lctx_1294_);
lean_ctor_set(v___x_1304_, 3, v_localInstances_1295_);
lean_ctor_set(v___x_1304_, 4, v_defEqCtx_x3f_1296_);
lean_ctor_set(v___x_1304_, 5, v_synthPendingDepth_1297_);
lean_ctor_set(v___x_1304_, 6, v_canUnfold_x3f_1298_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*7, v_trackZetaDelta_1292_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*7 + 1, v_univApprox_1299_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1300_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*7 + 3, v_cacheInferType_1301_);
v___x_1305_ = l_Lean_Meta_DiscrTree_mkPath(v_lhs_1286_, v___x_1271_, v___x_1304_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec_ref(v___x_1304_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1307_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref(v___x_1305_);
v___x_1307_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_a_1284_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec_ref(v___x_1307_);
v___x_1308_ = l_Lean_Meta_unificationHintExtension;
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v_declName_1262_);
lean_ctor_set(v___x_1288_, 0, v_a_1306_);
v___x_1310_ = v___x_1288_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_declName_1262_);
v___x_1310_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v___x_1308_, v___x_1310_, v_kind_1263_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1311_;
}
}
else
{
lean_dec(v_a_1306_);
lean_del_object(v___x_1288_);
lean_dec(v_declName_1262_);
return v___x_1307_;
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_del_object(v___x_1288_);
lean_dec(v_a_1284_);
lean_dec(v_declName_1262_);
v_a_1313_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1305_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1305_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_declName_1262_);
v_a_1323_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1277_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1277_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_declName_1262_);
v_a_1331_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1269_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1269_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object* v_declName_1339_, lean_object* v_kind_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_kind_boxed_1346_; lean_object* v_res_1347_; 
v_kind_boxed_1346_ = lean_unbox(v_kind_1340_);
v_res_1347_ = l_Lean_Meta_addUnificationHint___lam__0(v_declName_1339_, v_kind_boxed_1346_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* v_declName_1348_, uint8_t v_kind_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v___f_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1355_ = lean_box(v_kind_1349_);
v___f_1356_ = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1356_, 0, v_declName_1348_);
lean_closure_set(v___f_1356_, 1, v___x_1355_);
v___x_1357_ = 0;
v___x_1358_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v___f_1356_, v___x_1357_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* v_declName_1359_, lean_object* v_kind_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
uint8_t v_kind_boxed_1366_; lean_object* v_res_1367_; 
v_kind_boxed_1366_ = lean_unbox(v_kind_1360_);
v_res_1367_ = l_Lean_Meta_addUnificationHint(v_declName_1359_, v_kind_boxed_1366_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object* v_00_u03b1_1368_, lean_object* v_constName_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_constName_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(v_00_u03b1_1376_, v_constName_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1384_, lean_object* v_ref_1385_, lean_object* v_constName_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1385_, v_constName_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1393_, lean_object* v_ref_1394_, lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(v_00_u03b1_1393_, v_ref_1394_, v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v_ref_1394_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_1402_, lean_object* v_ref_1403_, lean_object* v_msg_1404_, lean_object* v_declHint_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1403_, v_msg_1404_, v_declHint_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1412_, lean_object* v_ref_1413_, lean_object* v_msg_1414_, lean_object* v_declHint_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(v_00_u03b1_1412_, v_ref_1413_, v_msg_1414_, v_declHint_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v_ref_1413_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1422_, lean_object* v_declHint_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1422_, v_declHint_1423_, v___y_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1430_, lean_object* v_declHint_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(v_msg_1430_, v_declHint_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1438_, lean_object* v_ref_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1439_, v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1447_, lean_object* v_ref_1448_, lean_object* v_msg_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(v_00_u03b1_1447_, v_ref_1448_, v_msg_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v_ref_1448_);
return v_res_1455_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1462_; uint64_t v___x_1463_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1463_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1462_);
return v___x_1463_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1465_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1466_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set_uint64(v___x_1466_, sizeof(void*)*1, v___x_1464_);
return v___x_1466_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1467_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1471_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
lean_ctor_set(v___x_1471_, 2, v___x_1470_);
lean_ctor_set(v___x_1471_, 3, v___x_1470_);
lean_ctor_set(v___x_1471_, 4, v___x_1470_);
lean_ctor_set(v___x_1471_, 5, v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
lean_ctor_set(v___x_1473_, 2, v___x_1472_);
lean_ctor_set(v___x_1473_, 3, v___x_1472_);
lean_ctor_set(v___x_1473_, 4, v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1474_, lean_object* v___x_1475_, lean_object* v_declName_1476_, lean_object* v_stx_1477_, uint8_t v_kind_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1477_, v___y_1479_, v___y_1480_);
if (lean_obj_tag(v___x_1482_) == 0)
{
uint8_t v___x_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec_ref(v___x_1482_);
v___x_1483_ = 0;
v___x_1484_ = 1;
v___x_1485_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1486_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1487_ = lean_unsigned_to_nat(32u);
v___x_1488_ = lean_mk_empty_array_with_capacity(v___x_1487_);
v___x_1489_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1490_ = ((size_t)5ULL);
lean_inc_n(v___x_1474_, 5);
v___x_1491_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1488_);
lean_ctor_set(v___x_1491_, 2, v___x_1474_);
lean_ctor_set(v___x_1491_, 3, v___x_1474_);
lean_ctor_set_usize(v___x_1491_, 4, v___x_1490_);
v___x_1492_ = lean_box(1);
lean_inc_ref(v___x_1491_);
v___x_1493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1486_);
lean_ctor_set(v___x_1493_, 1, v___x_1491_);
lean_ctor_set(v___x_1493_, 2, v___x_1492_);
v___x_1494_ = lean_mk_empty_array_with_capacity(v___x_1474_);
v___x_1495_ = lean_box(0);
lean_inc(v___x_1475_);
v___x_1496_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1496_, 0, v___x_1485_);
lean_ctor_set(v___x_1496_, 1, v___x_1475_);
lean_ctor_set(v___x_1496_, 2, v___x_1493_);
lean_ctor_set(v___x_1496_, 3, v___x_1494_);
lean_ctor_set(v___x_1496_, 4, v___x_1495_);
lean_ctor_set(v___x_1496_, 5, v___x_1474_);
lean_ctor_set(v___x_1496_, 6, v___x_1495_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*7, v___x_1483_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*7 + 1, v___x_1483_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*7 + 2, v___x_1483_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*7 + 3, v___x_1484_);
v___x_1497_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1474_);
lean_ctor_set(v___x_1497_, 1, v___x_1474_);
lean_ctor_set(v___x_1497_, 2, v___x_1474_);
lean_ctor_set(v___x_1497_, 3, v___x_1486_);
lean_ctor_set(v___x_1497_, 4, v___x_1486_);
lean_ctor_set(v___x_1497_, 5, v___x_1486_);
lean_ctor_set(v___x_1497_, 6, v___x_1486_);
lean_ctor_set(v___x_1497_, 7, v___x_1486_);
lean_ctor_set(v___x_1497_, 8, v___x_1486_);
v___x_1498_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1499_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1497_);
lean_ctor_set(v___x_1500_, 1, v___x_1498_);
lean_ctor_set(v___x_1500_, 2, v___x_1475_);
lean_ctor_set(v___x_1500_, 3, v___x_1491_);
lean_ctor_set(v___x_1500_, 4, v___x_1499_);
v___x_1501_ = lean_st_mk_ref(v___x_1500_);
v___x_1502_ = l_Lean_Meta_addUnificationHint(v_declName_1476_, v_kind_1478_, v___x_1496_, v___x_1501_, v___y_1479_, v___y_1480_);
lean_dec_ref(v___x_1496_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1511_; 
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v___x_1502_, 0);
lean_dec(v_unused_1512_);
v___x_1504_ = v___x_1502_;
v_isShared_1505_ = v_isSharedCheck_1511_;
goto v_resetjp_1503_;
}
else
{
lean_dec(v___x_1502_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1511_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1506_ = lean_st_ref_get(v___x_1501_);
lean_dec(v___x_1501_);
lean_dec(v___x_1506_);
v___x_1507_ = lean_box(0);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1507_);
v___x_1509_ = v___x_1504_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
else
{
lean_dec(v___x_1501_);
return v___x_1502_;
}
}
else
{
lean_dec(v_declName_1476_);
lean_dec(v___x_1475_);
lean_dec(v___x_1474_);
return v___x_1482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1513_, lean_object* v___x_1514_, lean_object* v_declName_1515_, lean_object* v_stx_1516_, lean_object* v_kind_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v_kind_boxed_1521_; lean_object* v_res_1522_; 
v_kind_boxed_1521_ = lean_unbox(v_kind_1517_);
v_res_1522_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1513_, v___x_1514_, v_declName_1515_, v_stx_1516_, v_kind_boxed_1521_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v_env_1528_; lean_object* v_options_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1527_ = lean_st_ref_get(v___y_1525_);
v_env_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc_ref(v_env_1528_);
lean_dec(v___x_1527_);
v_options_1529_ = lean_ctor_get(v___y_1524_, 2);
v___x_1530_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1531_ = lean_unsigned_to_nat(32u);
v___x_1532_ = lean_mk_empty_array_with_capacity(v___x_1531_);
lean_dec_ref(v___x_1532_);
v___x_1533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_1529_);
v___x_1534_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1534_, 0, v_env_1528_);
lean_ctor_set(v___x_1534_, 1, v___x_1530_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
lean_ctor_set(v___x_1534_, 3, v_options_1529_);
v___x_1535_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v_msgData_1523_);
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_ref_1546_; lean_object* v___x_1547_; lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1556_; 
v_ref_1546_ = lean_ctor_get(v___y_1543_, 5);
v___x_1547_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msg_1542_, v___y_1543_, v___y_1544_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_inc(v_ref_1546_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_ref_1546_);
lean_ctor_set(v___x_1552_, 1, v_a_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 1);
lean_ctor_set(v___x_1550_, 0, v___x_1552_);
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1561_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1564_ = l_Lean_stringToMessageData(v___x_1563_);
return v___x_1564_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1568_, lean_object* v_decl_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1573_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1574_ = l_Lean_MessageData_ofName(v___x_1568_);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v___x_1577_, v___y_1570_, v___y_1571_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1579_, lean_object* v_decl_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1579_, v_decl_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v_decl_1580_);
return v_res_1584_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_unsigned_to_nat(3033092106u);
v___x_1629_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1630_ = l_Lean_Name_num___override(v___x_1629_, v___x_1628_);
return v___x_1630_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1633_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1634_ = l_Lean_Name_str___override(v___x_1633_, v___x_1632_);
return v___x_1634_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1637_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1638_ = l_Lean_Name_str___override(v___x_1637_, v___x_1636_);
return v___x_1638_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = lean_unsigned_to_nat(2u);
v___x_1640_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1641_ = l_Lean_Name_num___override(v___x_1640_, v___x_1639_);
return v___x_1641_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1648_ = 0;
v___x_1649_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1650_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1651_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1652_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v___x_1650_);
lean_ctor_set(v___x_1652_, 2, v___x_1649_);
lean_ctor_set_uint8(v___x_1652_, sizeof(void*)*3, v___x_1648_);
return v___x_1652_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___f_1653_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___f_1654_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1655_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v___f_1654_);
lean_ctor_set(v___x_1656_, 2, v___f_1653_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1659_ = l_Lean_registerBuiltinAttribute(v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1662_, lean_object* v_msg_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1663_, v___y_1664_, v___y_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1668_, lean_object* v_msg_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(v_00_u03b1_1668_, v_msg_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1673_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0(void){
_start:
{
uint8_t v___x_1674_; uint64_t v___x_1675_; 
v___x_1674_ = 2;
v___x_1675_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* v_p_1676_, lean_object* v_e_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v___x_1683_; uint8_t v_foApprox_1684_; uint8_t v_ctxApprox_1685_; uint8_t v_quasiPatternApprox_1686_; uint8_t v_constApprox_1687_; uint8_t v_isDefEqStuckEx_1688_; uint8_t v_unificationHints_1689_; uint8_t v_proofIrrelevance_1690_; uint8_t v_assignSyntheticOpaque_1691_; uint8_t v_offsetCnstrs_1692_; uint8_t v_etaStruct_1693_; uint8_t v_univApprox_1694_; uint8_t v_iota_1695_; uint8_t v_beta_1696_; uint8_t v_proj_1697_; uint8_t v_zeta_1698_; uint8_t v_zetaDelta_1699_; uint8_t v_zetaUnused_1700_; uint8_t v_zetaHave_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1728_; 
v___x_1683_ = l_Lean_Meta_Context_config(v_a_1678_);
v_foApprox_1684_ = lean_ctor_get_uint8(v___x_1683_, 0);
v_ctxApprox_1685_ = lean_ctor_get_uint8(v___x_1683_, 1);
v_quasiPatternApprox_1686_ = lean_ctor_get_uint8(v___x_1683_, 2);
v_constApprox_1687_ = lean_ctor_get_uint8(v___x_1683_, 3);
v_isDefEqStuckEx_1688_ = lean_ctor_get_uint8(v___x_1683_, 4);
v_unificationHints_1689_ = lean_ctor_get_uint8(v___x_1683_, 5);
v_proofIrrelevance_1690_ = lean_ctor_get_uint8(v___x_1683_, 6);
v_assignSyntheticOpaque_1691_ = lean_ctor_get_uint8(v___x_1683_, 7);
v_offsetCnstrs_1692_ = lean_ctor_get_uint8(v___x_1683_, 8);
v_etaStruct_1693_ = lean_ctor_get_uint8(v___x_1683_, 10);
v_univApprox_1694_ = lean_ctor_get_uint8(v___x_1683_, 11);
v_iota_1695_ = lean_ctor_get_uint8(v___x_1683_, 12);
v_beta_1696_ = lean_ctor_get_uint8(v___x_1683_, 13);
v_proj_1697_ = lean_ctor_get_uint8(v___x_1683_, 14);
v_zeta_1698_ = lean_ctor_get_uint8(v___x_1683_, 15);
v_zetaDelta_1699_ = lean_ctor_get_uint8(v___x_1683_, 16);
v_zetaUnused_1700_ = lean_ctor_get_uint8(v___x_1683_, 17);
v_zetaHave_1701_ = lean_ctor_get_uint8(v___x_1683_, 18);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1703_ = v___x_1683_;
v_isShared_1704_ = v_isSharedCheck_1728_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v___x_1683_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1728_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
uint8_t v_trackZetaDelta_1705_; lean_object* v_zetaDeltaSet_1706_; lean_object* v_lctx_1707_; lean_object* v_localInstances_1708_; lean_object* v_defEqCtx_x3f_1709_; lean_object* v_synthPendingDepth_1710_; lean_object* v_canUnfold_x3f_1711_; uint8_t v_univApprox_1712_; uint8_t v_inTypeClassResolution_1713_; uint8_t v_cacheInferType_1714_; uint8_t v___x_1715_; lean_object* v_config_1717_; 
v_trackZetaDelta_1705_ = lean_ctor_get_uint8(v_a_1678_, sizeof(void*)*7);
v_zetaDeltaSet_1706_ = lean_ctor_get(v_a_1678_, 1);
v_lctx_1707_ = lean_ctor_get(v_a_1678_, 2);
v_localInstances_1708_ = lean_ctor_get(v_a_1678_, 3);
v_defEqCtx_x3f_1709_ = lean_ctor_get(v_a_1678_, 4);
v_synthPendingDepth_1710_ = lean_ctor_get(v_a_1678_, 5);
v_canUnfold_x3f_1711_ = lean_ctor_get(v_a_1678_, 6);
v_univApprox_1712_ = lean_ctor_get_uint8(v_a_1678_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1713_ = lean_ctor_get_uint8(v_a_1678_, sizeof(void*)*7 + 2);
v_cacheInferType_1714_ = lean_ctor_get_uint8(v_a_1678_, sizeof(void*)*7 + 3);
v___x_1715_ = 2;
if (v_isShared_1704_ == 0)
{
v_config_1717_ = v___x_1703_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 0, v_foApprox_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 1, v_ctxApprox_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 2, v_quasiPatternApprox_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 3, v_constApprox_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 4, v_isDefEqStuckEx_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 5, v_unificationHints_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 6, v_proofIrrelevance_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 7, v_assignSyntheticOpaque_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 8, v_offsetCnstrs_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 10, v_etaStruct_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 11, v_univApprox_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 12, v_iota_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 13, v_beta_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 14, v_proj_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 15, v_zeta_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 16, v_zetaDelta_1699_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 17, v_zetaUnused_1700_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, 18, v_zetaHave_1701_);
v_config_1717_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
uint64_t v___x_1718_; uint64_t v___x_1719_; uint64_t v___x_1720_; uint64_t v___x_1721_; uint64_t v___x_1722_; uint64_t v_key_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_ctor_set_uint8(v_config_1717_, 9, v___x_1715_);
v___x_1718_ = l_Lean_Meta_Context_configKey(v_a_1678_);
v___x_1719_ = 2ULL;
v___x_1720_ = lean_uint64_shift_right(v___x_1718_, v___x_1719_);
v___x_1721_ = lean_uint64_shift_left(v___x_1720_, v___x_1719_);
v___x_1722_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0);
v_key_1723_ = lean_uint64_lor(v___x_1721_, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1724_, 0, v_config_1717_);
lean_ctor_set_uint64(v___x_1724_, sizeof(void*)*1, v_key_1723_);
lean_inc(v_canUnfold_x3f_1711_);
lean_inc(v_synthPendingDepth_1710_);
lean_inc(v_defEqCtx_x3f_1709_);
lean_inc_ref(v_localInstances_1708_);
lean_inc_ref(v_lctx_1707_);
lean_inc(v_zetaDeltaSet_1706_);
v___x_1725_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
lean_ctor_set(v___x_1725_, 1, v_zetaDeltaSet_1706_);
lean_ctor_set(v___x_1725_, 2, v_lctx_1707_);
lean_ctor_set(v___x_1725_, 3, v_localInstances_1708_);
lean_ctor_set(v___x_1725_, 4, v_defEqCtx_x3f_1709_);
lean_ctor_set(v___x_1725_, 5, v_synthPendingDepth_1710_);
lean_ctor_set(v___x_1725_, 6, v_canUnfold_x3f_1711_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*7, v_trackZetaDelta_1705_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*7 + 1, v_univApprox_1712_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1713_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*7 + 3, v_cacheInferType_1714_);
lean_inc(v_a_1681_);
lean_inc_ref(v_a_1680_);
lean_inc(v_a_1679_);
v___x_1726_ = lean_is_expr_def_eq(v_p_1676_, v_e_1677_, v___x_1725_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object* v_p_1729_, lean_object* v_e_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_p_1729_, v_e_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object* v_x_1737_, lean_object* v_x_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
if (lean_obj_tag(v_x_1737_) == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = l_List_reverse___redArg(v_x_1738_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
else
{
lean_object* v_tail_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1764_; 
v_tail_1746_ = lean_ctor_get(v_x_1737_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_x_1737_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; 
v_unused_1765_ = lean_ctor_get(v_x_1737_, 0);
lean_dec(v_unused_1765_);
v___x_1748_ = v_x_1737_;
v_isShared_1749_ = v_isSharedCheck_1764_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_tail_1746_);
lean_dec(v_x_1737_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1764_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v_x_1738_);
lean_ctor_set(v___x_1748_, 0, v_a_1751_);
v___x_1753_ = v___x_1748_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1751_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_x_1738_);
v___x_1753_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
v_x_1737_ = v_tail_1746_;
v_x_1738_ = v___x_1753_;
goto _start;
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_del_object(v___x_1748_);
lean_dec(v_tail_1746_);
lean_dec(v_x_1738_);
v_a_1756_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1750_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1750_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object* v_x_1766_, lean_object* v_x_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v_x_1766_, v_x_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1773_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1774_; double v___x_1775_; 
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = lean_float_of_nat(v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object* v_cls_1779_, lean_object* v_msg_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_ref_1786_; lean_object* v___x_1787_; lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1832_; 
v_ref_1786_ = lean_ctor_get(v___y_1783_, 5);
v___x_1787_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1832_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1832_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v_traceState_1793_; lean_object* v_env_1794_; lean_object* v_nextMacroScope_1795_; lean_object* v_ngen_1796_; lean_object* v_auxDeclNGen_1797_; lean_object* v_cache_1798_; lean_object* v_messages_1799_; lean_object* v_infoState_1800_; lean_object* v_snapshotTasks_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1831_; 
v___x_1792_ = lean_st_ref_take(v___y_1784_);
v_traceState_1793_ = lean_ctor_get(v___x_1792_, 4);
v_env_1794_ = lean_ctor_get(v___x_1792_, 0);
v_nextMacroScope_1795_ = lean_ctor_get(v___x_1792_, 1);
v_ngen_1796_ = lean_ctor_get(v___x_1792_, 2);
v_auxDeclNGen_1797_ = lean_ctor_get(v___x_1792_, 3);
v_cache_1798_ = lean_ctor_get(v___x_1792_, 5);
v_messages_1799_ = lean_ctor_get(v___x_1792_, 6);
v_infoState_1800_ = lean_ctor_get(v___x_1792_, 7);
v_snapshotTasks_1801_ = lean_ctor_get(v___x_1792_, 8);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1803_ = v___x_1792_;
v_isShared_1804_ = v_isSharedCheck_1831_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_snapshotTasks_1801_);
lean_inc(v_infoState_1800_);
lean_inc(v_messages_1799_);
lean_inc(v_cache_1798_);
lean_inc(v_traceState_1793_);
lean_inc(v_auxDeclNGen_1797_);
lean_inc(v_ngen_1796_);
lean_inc(v_nextMacroScope_1795_);
lean_inc(v_env_1794_);
lean_dec(v___x_1792_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1831_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
uint64_t v_tid_1805_; lean_object* v_traces_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1830_; 
v_tid_1805_ = lean_ctor_get_uint64(v_traceState_1793_, sizeof(void*)*1);
v_traces_1806_ = lean_ctor_get(v_traceState_1793_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_traceState_1793_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1808_ = v_traceState_1793_;
v_isShared_1809_ = v_isSharedCheck_1830_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_traces_1806_);
lean_dec(v_traceState_1793_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1830_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; double v___x_1811_; uint8_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
v___x_1812_ = 0;
v___x_1813_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_1814_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1814_, 0, v_cls_1779_);
lean_ctor_set(v___x_1814_, 1, v___x_1810_);
lean_ctor_set(v___x_1814_, 2, v___x_1813_);
lean_ctor_set_float(v___x_1814_, sizeof(void*)*3, v___x_1811_);
lean_ctor_set_float(v___x_1814_, sizeof(void*)*3 + 8, v___x_1811_);
lean_ctor_set_uint8(v___x_1814_, sizeof(void*)*3 + 16, v___x_1812_);
v___x_1815_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2));
v___x_1816_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v_a_1788_);
lean_ctor_set(v___x_1816_, 2, v___x_1815_);
lean_inc(v_ref_1786_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_ref_1786_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = l_Lean_PersistentArray_push___redArg(v_traces_1806_, v___x_1817_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1818_);
v___x_1820_ = v___x_1808_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1818_);
lean_ctor_set_uint64(v_reuseFailAlloc_1829_, sizeof(void*)*1, v_tid_1805_);
v___x_1820_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 4, v___x_1820_);
v___x_1822_ = v___x_1803_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_env_1794_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_nextMacroScope_1795_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_ngen_1796_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v_auxDeclNGen_1797_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1828_, 5, v_cache_1798_);
lean_ctor_set(v_reuseFailAlloc_1828_, 6, v_messages_1799_);
lean_ctor_set(v_reuseFailAlloc_1828_, 7, v_infoState_1800_);
lean_ctor_set(v_reuseFailAlloc_1828_, 8, v_snapshotTasks_1801_);
v___x_1822_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1823_ = lean_st_ref_set(v___y_1784_, v___x_1822_);
v___x_1824_ = lean_box(0);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1824_);
v___x_1826_ = v___x_1790_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object* v_cls_1833_, lean_object* v_msg_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_1833_, v_msg_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object* v_as_1844_, size_t v_sz_1845_, size_t v_i_1846_, lean_object* v_b_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_a_1854_; uint8_t v___x_1858_; 
v___x_1858_ = lean_usize_dec_lt(v_i_1846_, v_sz_1845_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_b_1847_);
return v___x_1859_;
}
else
{
lean_object* v_snd_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1950_; 
v_snd_1860_ = lean_ctor_get(v_b_1847_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_b_1847_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v_b_1847_, 0);
lean_dec(v_unused_1951_);
v___x_1862_ = v_b_1847_;
v_isShared_1863_ = v_isSharedCheck_1950_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_snd_1860_);
lean_dec(v_b_1847_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1950_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_array_1864_; lean_object* v_start_1865_; lean_object* v_stop_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v_array_1864_ = lean_ctor_get(v_snd_1860_, 0);
v_start_1865_ = lean_ctor_get(v_snd_1860_, 1);
v_stop_1866_ = lean_ctor_get(v_snd_1860_, 2);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_nat_dec_lt(v_start_1865_, v_stop_1866_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1870_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1867_);
v___x_1870_ = v___x_1862_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_snd_1860_);
v___x_1870_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
}
else
{
lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1946_; 
lean_inc(v_stop_1866_);
lean_inc(v_start_1865_);
lean_inc_ref(v_array_1864_);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_snd_1860_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; lean_object* v_unused_1948_; lean_object* v_unused_1949_; 
v_unused_1947_ = lean_ctor_get(v_snd_1860_, 2);
lean_dec(v_unused_1947_);
v_unused_1948_ = lean_ctor_get(v_snd_1860_, 1);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_snd_1860_, 0);
lean_dec(v_unused_1949_);
v___x_1874_ = v_snd_1860_;
v_isShared_1875_ = v_isSharedCheck_1946_;
goto v_resetjp_1873_;
}
else
{
lean_dec(v_snd_1860_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1946_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1876_ = lean_array_fget(v_array_1864_, v_start_1865_);
v___x_1877_ = lean_unsigned_to_nat(1u);
v___x_1878_ = lean_nat_add(v_start_1865_, v___x_1877_);
lean_dec(v_start_1865_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 1, v___x_1878_);
v___x_1880_ = v___x_1874_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_array_1864_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_stop_1866_);
v___x_1880_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
uint8_t v___x_1881_; uint8_t v___x_1882_; uint8_t v___x_1883_; 
v___x_1881_ = 3;
v___x_1882_ = lean_unbox(v___x_1876_);
lean_dec(v___x_1876_);
v___x_1883_ = l_Lean_instBEqBinderInfo_beq(v___x_1882_, v___x_1881_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1885_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v___x_1880_);
lean_ctor_set(v___x_1862_, 0, v___x_1867_);
v___x_1885_ = v___x_1862_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v___x_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
v_a_1854_ = v___x_1885_;
goto v___jp_1853_;
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1888_; 
v_a_1887_ = lean_array_uget_borrowed(v_as_1844_, v_i_1846_);
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1850_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
lean_inc(v_a_1887_);
v___x_1888_ = lean_infer_type(v_a_1887_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l_Lean_Meta_trySynthInstance(v_a_1889_, v___x_1867_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1928_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1928_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1928_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
if (lean_obj_tag(v_a_1891_) == 1)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; 
lean_del_object(v___x_1893_);
v_a_1895_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_a_1895_);
lean_dec_ref(v_a_1891_);
lean_inc(v_a_1887_);
v___x_1896_ = l_Lean_Meta_isExprDefEq(v_a_1887_, v_a_1895_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1912_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1912_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1912_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
uint8_t v___x_1901_; 
v___x_1901_ = lean_unbox(v_a_1897_);
lean_dec(v_a_1897_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v___x_1880_);
lean_ctor_set(v___x_1862_, 0, v___x_1902_);
v___x_1904_ = v___x_1862_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v___x_1880_);
v___x_1904_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1906_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1904_);
v___x_1906_ = v___x_1899_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_object* v___x_1910_; 
lean_del_object(v___x_1899_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v___x_1880_);
lean_ctor_set(v___x_1862_, 0, v___x_1867_);
v___x_1910_ = v___x_1862_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v___x_1880_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
v_a_1854_ = v___x_1910_;
goto v___jp_1853_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v___x_1880_);
lean_del_object(v___x_1862_);
v_a_1913_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1896_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1896_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
lean_dec(v_a_1891_);
v___x_1921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v___x_1880_);
lean_ctor_set(v___x_1862_, 0, v___x_1921_);
v___x_1923_ = v___x_1862_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1880_);
v___x_1923_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1925_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1923_);
v___x_1925_ = v___x_1893_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
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
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v___x_1880_);
lean_del_object(v___x_1862_);
v_a_1929_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1890_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1890_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v___x_1880_);
lean_del_object(v___x_1862_);
v_a_1937_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1888_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1888_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
}
}
}
v___jp_1853_:
{
size_t v___x_1855_; size_t v___x_1856_; 
v___x_1855_ = ((size_t)1ULL);
v___x_1856_ = lean_usize_add(v_i_1846_, v___x_1855_);
v_i_1846_ = v___x_1856_;
v_b_1847_ = v_a_1854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object* v_as_1952_, lean_object* v_sz_1953_, lean_object* v_i_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
size_t v_sz_boxed_1961_; size_t v_i_boxed_1962_; lean_object* v_res_1963_; 
v_sz_boxed_1961_ = lean_unbox_usize(v_sz_1953_);
lean_dec(v_sz_1953_);
v_i_boxed_1962_ = lean_unbox_usize(v_i_1954_);
lean_dec(v_i_1954_);
v_res_1963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_as_1952_, v_sz_boxed_1961_, v_i_boxed_1962_, v_b_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec_ref(v_as_1952_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object* v_as_x27_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
if (lean_obj_tag(v_as_x27_1967_) == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_b_1968_);
return v___x_1974_;
}
else
{
lean_object* v_head_1975_; lean_object* v_tail_1976_; lean_object* v_lhs_1977_; lean_object* v_rhs_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v_b_1968_);
v_head_1975_ = lean_ctor_get(v_as_x27_1967_, 0);
lean_inc(v_head_1975_);
v_tail_1976_ = lean_ctor_get(v_as_x27_1967_, 1);
lean_inc(v_tail_1976_);
lean_dec_ref(v_as_x27_1967_);
v_lhs_1977_ = lean_ctor_get(v_head_1975_, 0);
v_rhs_1978_ = lean_ctor_get(v_head_1975_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_head_1975_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1980_ = v_head_1975_;
v_isShared_1981_ = v_isSharedCheck_2007_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_rhs_1978_);
lean_inc(v_lhs_1977_);
lean_dec(v_head_1975_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2007_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; 
lean_inc(v___y_1972_);
lean_inc_ref(v___y_1971_);
lean_inc(v___y_1970_);
lean_inc_ref(v___y_1969_);
v___x_1982_ = lean_is_expr_def_eq(v_lhs_1977_, v_rhs_1978_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1998_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_1998_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1998_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = lean_box(0);
v___x_1988_ = lean_unbox(v_a_1983_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_dec(v_tail_1976_);
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1983_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v___x_1987_);
lean_ctor_set(v___x_1980_, 0, v___x_1989_);
v___x_1991_ = v___x_1980_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1987_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1991_);
v___x_1993_ = v___x_1985_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_object* v___x_1996_; 
lean_del_object(v___x_1985_);
lean_dec(v_a_1983_);
lean_del_object(v___x_1980_);
v___x_1996_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_as_x27_1967_ = v_tail_1976_;
v_b_1968_ = v___x_1996_;
goto _start;
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_del_object(v___x_1980_);
lean_dec(v_tail_1976_);
v_a_1999_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1982_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1982_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object* v_as_x27_2008_, lean_object* v_b_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2008_, v_b_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
return v_res_2015_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2016_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8(void){
_start:
{
lean_object* v_cls_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_cls_2031_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2032_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7));
v___x_2033_ = l_Lean_Name_append(v___x_2032_, v_cls_2031_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9));
v___x_2036_ = l_Lean_stringToMessageData(v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object* v_candidate_2037_, lean_object* v_t_2038_, lean_object* v_s_2039_, uint8_t v_mayPostpone_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_Meta_saveState___redArg(v_a_2042_, v_a_2044_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2297_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2297_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2297_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___y_2052_; uint8_t v___y_2053_; lean_object* v_a_2075_; uint8_t v_a_2079_; lean_object* v___x_2091_; lean_object* v_cache_2092_; lean_object* v_mctx_2093_; lean_object* v_zetaDeltaFVarIds_2094_; lean_object* v_postponed_2095_; lean_object* v_diag_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2296_; 
v___x_2091_ = lean_st_ref_take(v_a_2042_);
v_cache_2092_ = lean_ctor_get(v___x_2091_, 1);
v_mctx_2093_ = lean_ctor_get(v___x_2091_, 0);
v_zetaDeltaFVarIds_2094_ = lean_ctor_get(v___x_2091_, 2);
v_postponed_2095_ = lean_ctor_get(v___x_2091_, 3);
v_diag_2096_ = lean_ctor_get(v___x_2091_, 4);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2098_ = v___x_2091_;
v_isShared_2099_ = v_isSharedCheck_2296_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_diag_2096_);
lean_inc(v_postponed_2095_);
lean_inc(v_zetaDeltaFVarIds_2094_);
lean_inc(v_cache_2092_);
lean_inc(v_mctx_2093_);
lean_dec(v___x_2091_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2296_;
goto v_resetjp_2097_;
}
v___jp_2051_:
{
if (v___y_2053_ == 0)
{
lean_object* v___x_2054_; 
lean_del_object(v___x_2049_);
v___x_2054_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2047_, v_a_2042_, v_a_2044_);
lean_dec(v_a_2047_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v___x_2054_, 0);
lean_dec(v_unused_2062_);
v___x_2056_ = v___x_2054_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_dec(v___x_2054_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 1);
lean_ctor_set(v___x_2056_, 0, v___y_2052_);
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___y_2052_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref(v___y_2052_);
v_a_2063_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2054_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2054_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v___x_2072_; 
lean_dec(v_a_2047_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set_tag(v___x_2049_, 1);
lean_ctor_set(v___x_2049_, 0, v___y_2052_);
v___x_2072_ = v___x_2049_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___y_2052_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
v___jp_2074_:
{
uint8_t v___x_2076_; 
v___x_2076_ = l_Lean_Exception_isInterrupt(v_a_2075_);
if (v___x_2076_ == 0)
{
uint8_t v___x_2077_; 
lean_inc_ref(v_a_2075_);
v___x_2077_ = l_Lean_Exception_isRuntime(v_a_2075_);
v___y_2052_ = v_a_2075_;
v___y_2053_ = v___x_2077_;
goto v___jp_2051_;
}
else
{
v___y_2052_ = v_a_2075_;
v___y_2053_ = v___x_2076_;
goto v___jp_2051_;
}
}
v___jp_2078_:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2047_, v_a_2042_, v_a_2044_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2088_; 
lean_del_object(v___x_2049_);
lean_dec(v_a_2047_);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; 
v_unused_2089_ = lean_ctor_get(v___x_2080_, 0);
lean_dec(v_unused_2089_);
v___x_2082_ = v___x_2080_;
v_isShared_2083_ = v_isSharedCheck_2088_;
goto v_resetjp_2081_;
}
else
{
lean_dec(v___x_2080_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2088_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = lean_box(v_a_2079_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2084_);
v___x_2086_ = v___x_2082_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
else
{
lean_object* v_a_2090_; 
v_a_2090_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2080_);
v_a_2075_ = v_a_2090_;
goto v___jp_2074_;
}
}
v_resetjp_2097_:
{
lean_object* v_inferType_2100_; lean_object* v_funInfo_2101_; lean_object* v_synthInstance_2102_; lean_object* v_whnf_2103_; lean_object* v_defEqPerm_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2294_; 
v_inferType_2100_ = lean_ctor_get(v_cache_2092_, 0);
v_funInfo_2101_ = lean_ctor_get(v_cache_2092_, 1);
v_synthInstance_2102_ = lean_ctor_get(v_cache_2092_, 2);
v_whnf_2103_ = lean_ctor_get(v_cache_2092_, 3);
v_defEqPerm_2104_ = lean_ctor_get(v_cache_2092_, 5);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_cache_2092_);
if (v_isSharedCheck_2294_ == 0)
{
lean_object* v_unused_2295_; 
v_unused_2295_ = lean_ctor_get(v_cache_2092_, 4);
lean_dec(v_unused_2295_);
v___x_2106_ = v_cache_2092_;
v_isShared_2107_ = v_isSharedCheck_2294_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_defEqPerm_2104_);
lean_inc(v_whnf_2103_);
lean_inc(v_synthInstance_2102_);
lean_inc(v_funInfo_2101_);
lean_inc(v_inferType_2100_);
lean_dec(v_cache_2092_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2294_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 4, v___x_2108_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_inferType_2100_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_funInfo_2101_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_synthInstance_2102_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_whnf_2103_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2293_, 5, v_defEqPerm_2104_);
v___x_2110_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v___x_2110_);
v___x_2112_ = v___x_2098_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_mctx_2093_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_zetaDeltaFVarIds_2094_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v_postponed_2095_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v_diag_2096_);
v___x_2112_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_st_ref_set(v_a_2042_, v___x_2112_);
v___x_2114_ = l_Lean_Meta_getResetPostponed___redArg(v_a_2042_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; uint8_t v_a_2117_; lean_object* v___x_2158_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref(v___x_2114_);
lean_inc(v_candidate_2037_);
v___x_2158_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_candidate_2037_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref(v___x_2158_);
v___x_2160_ = l_Lean_ConstantInfo_levelParams(v_a_2159_);
v___x_2161_ = lean_box(0);
v___x_2162_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v___x_2160_, v___x_2161_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___x_2162_);
v___x_2164_ = 0;
v___x_2165_ = l_Lean_Core_instantiateValueLevelParams(v_a_2159_, v_a_2163_, v___x_2164_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2159_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref(v___x_2165_);
v___x_2167_ = lean_box(0);
v___x_2168_ = l_Lean_Meta_lambdaMetaTelescope(v_a_2166_, v___x_2167_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2166_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v_snd_2170_; lean_object* v_fst_2171_; lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; uint8_t v_foApprox_2175_; uint8_t v_ctxApprox_2176_; uint8_t v_quasiPatternApprox_2177_; uint8_t v_constApprox_2178_; uint8_t v_isDefEqStuckEx_2179_; uint8_t v_proofIrrelevance_2180_; uint8_t v_assignSyntheticOpaque_2181_; uint8_t v_offsetCnstrs_2182_; uint8_t v_transparency_2183_; uint8_t v_etaStruct_2184_; uint8_t v_univApprox_2185_; uint8_t v_iota_2186_; uint8_t v_beta_2187_; uint8_t v_proj_2188_; uint8_t v_zeta_2189_; uint8_t v_zetaDelta_2190_; uint8_t v_zetaUnused_2191_; uint8_t v_zetaHave_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2279_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref(v___x_2168_);
v_snd_2170_ = lean_ctor_get(v_a_2169_, 1);
lean_inc(v_snd_2170_);
v_fst_2171_ = lean_ctor_get(v_a_2169_, 0);
lean_inc(v_fst_2171_);
lean_dec(v_a_2169_);
v_fst_2172_ = lean_ctor_get(v_snd_2170_, 0);
lean_inc(v_fst_2172_);
v_snd_2173_ = lean_ctor_get(v_snd_2170_, 1);
lean_inc(v_snd_2173_);
lean_dec(v_snd_2170_);
v___x_2174_ = l_Lean_Meta_Context_config(v_a_2041_);
v_foApprox_2175_ = lean_ctor_get_uint8(v___x_2174_, 0);
v_ctxApprox_2176_ = lean_ctor_get_uint8(v___x_2174_, 1);
v_quasiPatternApprox_2177_ = lean_ctor_get_uint8(v___x_2174_, 2);
v_constApprox_2178_ = lean_ctor_get_uint8(v___x_2174_, 3);
v_isDefEqStuckEx_2179_ = lean_ctor_get_uint8(v___x_2174_, 4);
v_proofIrrelevance_2180_ = lean_ctor_get_uint8(v___x_2174_, 6);
v_assignSyntheticOpaque_2181_ = lean_ctor_get_uint8(v___x_2174_, 7);
v_offsetCnstrs_2182_ = lean_ctor_get_uint8(v___x_2174_, 8);
v_transparency_2183_ = lean_ctor_get_uint8(v___x_2174_, 9);
v_etaStruct_2184_ = lean_ctor_get_uint8(v___x_2174_, 10);
v_univApprox_2185_ = lean_ctor_get_uint8(v___x_2174_, 11);
v_iota_2186_ = lean_ctor_get_uint8(v___x_2174_, 12);
v_beta_2187_ = lean_ctor_get_uint8(v___x_2174_, 13);
v_proj_2188_ = lean_ctor_get_uint8(v___x_2174_, 14);
v_zeta_2189_ = lean_ctor_get_uint8(v___x_2174_, 15);
v_zetaDelta_2190_ = lean_ctor_get_uint8(v___x_2174_, 16);
v_zetaUnused_2191_ = lean_ctor_get_uint8(v___x_2174_, 17);
v_zetaHave_2192_ = lean_ctor_get_uint8(v___x_2174_, 18);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2194_ = v___x_2174_;
v_isShared_2195_ = v_isSharedCheck_2279_;
goto v_resetjp_2193_;
}
else
{
lean_dec(v___x_2174_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2279_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_2173_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_dec_ref(v___x_2196_);
lean_del_object(v___x_2194_);
lean_dec(v_fst_2172_);
lean_dec(v_fst_2171_);
lean_dec(v_a_2115_);
lean_dec_ref(v_s_2039_);
lean_dec_ref(v_t_2038_);
lean_dec(v_candidate_2037_);
v_a_2079_ = v___x_2164_;
goto v___jp_2078_;
}
else
{
lean_object* v_a_2197_; uint8_t v_trackZetaDelta_2198_; lean_object* v_zetaDeltaSet_2199_; lean_object* v_lctx_2200_; lean_object* v_localInstances_2201_; lean_object* v_defEqCtx_x3f_2202_; lean_object* v_synthPendingDepth_2203_; lean_object* v_canUnfold_x3f_2204_; uint8_t v_univApprox_2205_; uint8_t v_inTypeClassResolution_2206_; uint8_t v_cacheInferType_2207_; lean_object* v_pattern_2208_; lean_object* v_constraints_2209_; uint8_t v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v_lhs_2242_; lean_object* v_rhs_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2278_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref(v___x_2196_);
v_trackZetaDelta_2198_ = lean_ctor_get_uint8(v_a_2041_, sizeof(void*)*7);
v_zetaDeltaSet_2199_ = lean_ctor_get(v_a_2041_, 1);
v_lctx_2200_ = lean_ctor_get(v_a_2041_, 2);
v_localInstances_2201_ = lean_ctor_get(v_a_2041_, 3);
v_defEqCtx_x3f_2202_ = lean_ctor_get(v_a_2041_, 4);
v_synthPendingDepth_2203_ = lean_ctor_get(v_a_2041_, 5);
v_canUnfold_x3f_2204_ = lean_ctor_get(v_a_2041_, 6);
v_univApprox_2205_ = lean_ctor_get_uint8(v_a_2041_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2206_ = lean_ctor_get_uint8(v_a_2041_, sizeof(void*)*7 + 2);
v_cacheInferType_2207_ = lean_ctor_get_uint8(v_a_2041_, sizeof(void*)*7 + 3);
v_pattern_2208_ = lean_ctor_get(v_a_2197_, 0);
lean_inc_ref(v_pattern_2208_);
v_constraints_2209_ = lean_ctor_get(v_a_2197_, 1);
lean_inc(v_constraints_2209_);
lean_dec(v_a_2197_);
v_lhs_2242_ = lean_ctor_get(v_pattern_2208_, 0);
v_rhs_2243_ = lean_ctor_get(v_pattern_2208_, 1);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_pattern_2208_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2245_ = v_pattern_2208_;
v_isShared_2246_ = v_isSharedCheck_2278_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_rhs_2243_);
lean_inc(v_lhs_2242_);
lean_dec(v_pattern_2208_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2278_;
goto v_resetjp_2244_;
}
v___jp_2210_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2217_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_constraints_2209_, v___x_2216_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v_fst_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2239_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref(v___x_2217_);
v_fst_2219_ = lean_ctor_get(v_a_2218_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_a_2218_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; 
v_unused_2240_ = lean_ctor_get(v_a_2218_, 1);
lean_dec(v_unused_2240_);
v___x_2221_ = v_a_2218_;
v_isShared_2222_ = v_isSharedCheck_2239_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_fst_2219_);
lean_dec(v_a_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2239_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
if (lean_obj_tag(v_fst_2219_) == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = lean_array_get_size(v_fst_2172_);
v___x_2225_ = l_Array_toSubarray___redArg(v_fst_2172_, v___x_2223_, v___x_2224_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v___x_2225_);
lean_ctor_set(v___x_2221_, 0, v___x_2167_);
v___x_2227_ = v___x_2221_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
size_t v_sz_2228_; size_t v___x_2229_; lean_object* v___x_2230_; 
v_sz_2228_ = lean_array_size(v_fst_2171_);
v___x_2229_ = ((size_t)0ULL);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_fst_2171_, v_sz_2228_, v___x_2229_, v___x_2227_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v_fst_2171_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v_fst_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref(v___x_2230_);
v_fst_2232_ = lean_ctor_get(v_a_2231_, 0);
lean_inc(v_fst_2232_);
lean_dec(v_a_2231_);
if (lean_obj_tag(v_fst_2232_) == 0)
{
v_a_2117_ = v___y_2211_;
goto v___jp_2116_;
}
else
{
lean_object* v_val_2233_; uint8_t v___x_2234_; 
v_val_2233_ = lean_ctor_get(v_fst_2232_, 0);
lean_inc(v_val_2233_);
lean_dec_ref(v_fst_2232_);
v___x_2234_ = lean_unbox(v_val_2233_);
lean_dec(v_val_2233_);
v_a_2117_ = v___x_2234_;
goto v___jp_2116_;
}
}
else
{
lean_object* v_a_2235_; 
lean_dec(v_a_2115_);
v_a_2235_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2235_);
lean_dec_ref(v___x_2230_);
v_a_2075_ = v_a_2235_;
goto v___jp_2074_;
}
}
}
else
{
lean_object* v_val_2237_; uint8_t v___x_2238_; 
lean_del_object(v___x_2221_);
lean_dec(v_fst_2172_);
lean_dec(v_fst_2171_);
v_val_2237_ = lean_ctor_get(v_fst_2219_, 0);
lean_inc(v_val_2237_);
lean_dec_ref(v_fst_2219_);
v___x_2238_ = lean_unbox(v_val_2237_);
lean_dec(v_val_2237_);
v_a_2117_ = v___x_2238_;
goto v___jp_2116_;
}
}
}
else
{
lean_object* v_a_2241_; 
lean_dec(v_fst_2172_);
lean_dec(v_fst_2171_);
lean_dec(v_a_2115_);
v_a_2241_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2241_);
lean_dec_ref(v___x_2217_);
v_a_2075_ = v_a_2241_;
goto v___jp_2074_;
}
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2195_ == 0)
{
v___x_2248_ = v___x_2194_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 0, v_foApprox_2175_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 1, v_ctxApprox_2176_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 2, v_quasiPatternApprox_2177_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 3, v_constApprox_2178_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 4, v_isDefEqStuckEx_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 6, v_proofIrrelevance_2180_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 7, v_assignSyntheticOpaque_2181_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 8, v_offsetCnstrs_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 9, v_transparency_2183_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 10, v_etaStruct_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 11, v_univApprox_2185_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 12, v_iota_2186_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 13, v_beta_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 14, v_proj_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 15, v_zeta_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 16, v_zetaDelta_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 17, v_zetaUnused_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, 18, v_zetaHave_2192_);
v___x_2248_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
uint64_t v___x_2249_; lean_object* v_cls_2250_; lean_object* v___y_2252_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_ctor_set_uint8(v___x_2248_, 5, v___x_2164_);
v___x_2249_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2248_);
v_cls_2250_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2271_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2271_, 0, v___x_2248_);
lean_ctor_set_uint64(v___x_2271_, sizeof(void*)*1, v___x_2249_);
lean_inc(v_canUnfold_x3f_2204_);
lean_inc(v_synthPendingDepth_2203_);
lean_inc(v_defEqCtx_x3f_2202_);
lean_inc_ref(v_localInstances_2201_);
lean_inc_ref(v_lctx_2200_);
lean_inc(v_zetaDeltaSet_2199_);
v___x_2272_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v_zetaDeltaSet_2199_);
lean_ctor_set(v___x_2272_, 2, v_lctx_2200_);
lean_ctor_set(v___x_2272_, 3, v_localInstances_2201_);
lean_ctor_set(v___x_2272_, 4, v_defEqCtx_x3f_2202_);
lean_ctor_set(v___x_2272_, 5, v_synthPendingDepth_2203_);
lean_ctor_set(v___x_2272_, 6, v_canUnfold_x3f_2204_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*7, v_trackZetaDelta_2198_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*7 + 1, v_univApprox_2205_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2206_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*7 + 3, v_cacheInferType_2207_);
v___x_2273_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_lhs_2242_, v_t_2038_, v___x_2272_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; uint8_t v___x_2275_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
v___x_2275_ = lean_unbox(v_a_2274_);
lean_dec(v_a_2274_);
if (v___x_2275_ == 0)
{
lean_dec_ref(v___x_2272_);
lean_dec_ref(v_rhs_2243_);
lean_dec_ref(v_s_2039_);
v___y_2252_ = v___x_2273_;
goto v___jp_2251_;
}
else
{
lean_object* v___x_2276_; 
lean_dec_ref(v___x_2273_);
v___x_2276_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_rhs_2243_, v_s_2039_, v___x_2272_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec_ref(v___x_2272_);
v___y_2252_ = v___x_2276_;
goto v___jp_2251_;
}
}
else
{
lean_dec_ref(v___x_2272_);
lean_dec_ref(v_rhs_2243_);
lean_dec_ref(v_s_2039_);
v___y_2252_ = v___x_2273_;
goto v___jp_2251_;
}
v___jp_2251_:
{
if (lean_obj_tag(v___y_2252_) == 0)
{
lean_object* v_a_2253_; uint8_t v___x_2254_; 
v_a_2253_ = lean_ctor_get(v___y_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___y_2252_);
v___x_2254_ = lean_unbox(v_a_2253_);
if (v___x_2254_ == 0)
{
lean_dec(v_a_2253_);
lean_del_object(v___x_2245_);
lean_dec(v_constraints_2209_);
lean_dec(v_fst_2172_);
lean_dec(v_fst_2171_);
lean_dec(v_a_2115_);
lean_dec(v_candidate_2037_);
v_a_2079_ = v___x_2164_;
goto v___jp_2078_;
}
else
{
lean_object* v_options_2255_; uint8_t v_hasTrace_2256_; 
v_options_2255_ = lean_ctor_get(v_a_2043_, 2);
v_hasTrace_2256_ = lean_ctor_get_uint8(v_options_2255_, sizeof(void*)*1);
if (v_hasTrace_2256_ == 0)
{
uint8_t v___x_2257_; 
lean_del_object(v___x_2245_);
lean_dec(v_candidate_2037_);
v___x_2257_ = lean_unbox(v_a_2253_);
lean_dec(v_a_2253_);
v___y_2211_ = v___x_2257_;
v___y_2212_ = v_a_2041_;
v___y_2213_ = v_a_2042_;
v___y_2214_ = v_a_2043_;
v___y_2215_ = v_a_2044_;
goto v___jp_2210_;
}
else
{
lean_object* v_inheritedTraceOptions_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v_inheritedTraceOptions_2258_ = lean_ctor_get(v_a_2043_, 13);
v___x_2259_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2260_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2258_, v_options_2255_, v___x_2259_);
if (v___x_2260_ == 0)
{
uint8_t v___x_2261_; 
lean_del_object(v___x_2245_);
lean_dec(v_candidate_2037_);
v___x_2261_ = lean_unbox(v_a_2253_);
lean_dec(v_a_2253_);
v___y_2211_ = v___x_2261_;
v___y_2212_ = v_a_2041_;
v___y_2213_ = v_a_2042_;
v___y_2214_ = v_a_2043_;
v___y_2215_ = v_a_2044_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2262_ = l_Lean_MessageData_ofName(v_candidate_2037_);
v___x_2263_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10);
if (v_isShared_2246_ == 0)
{
lean_ctor_set_tag(v___x_2245_, 7);
lean_ctor_set(v___x_2245_, 1, v___x_2263_);
lean_ctor_set(v___x_2245_, 0, v___x_2262_);
v___x_2265_ = v___x_2245_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2250_, v___x_2265_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2266_) == 0)
{
uint8_t v___x_2267_; 
lean_dec_ref(v___x_2266_);
v___x_2267_ = lean_unbox(v_a_2253_);
lean_dec(v_a_2253_);
v___y_2211_ = v___x_2267_;
v___y_2212_ = v_a_2041_;
v___y_2213_ = v_a_2042_;
v___y_2214_ = v_a_2043_;
v___y_2215_ = v_a_2044_;
goto v___jp_2210_;
}
else
{
lean_object* v_a_2268_; 
lean_dec(v_a_2253_);
lean_dec(v_constraints_2209_);
lean_dec(v_fst_2172_);
lean_dec(v_fst_2171_);
lean_dec(v_a_2115_);
v_a_2268_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2268_);
lean_dec_ref(v___x_2266_);
v_a_2075_ = v_a_2268_;
goto v___jp_2074_;
}
}
}
}
}
}
else
{
lean_object* v_a_2270_; 
lean_del_object(v___x_2245_);
lean_dec(v_constraints_2209_);
lean_dec(v_fst_2172_);
lean_dec(v_fst_2171_);
lean_dec(v_a_2115_);
lean_dec(v_candidate_2037_);
v_a_2270_ = lean_ctor_get(v___y_2252_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v___y_2252_);
v_a_2075_ = v_a_2270_;
goto v___jp_2074_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2280_; 
lean_dec(v_a_2115_);
lean_dec_ref(v_s_2039_);
lean_dec_ref(v_t_2038_);
lean_dec(v_candidate_2037_);
v_a_2280_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2168_);
v_a_2075_ = v_a_2280_;
goto v___jp_2074_;
}
}
else
{
lean_object* v_a_2281_; 
lean_dec(v_a_2115_);
lean_dec_ref(v_s_2039_);
lean_dec_ref(v_t_2038_);
lean_dec(v_candidate_2037_);
v_a_2281_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2281_);
lean_dec_ref(v___x_2165_);
v_a_2075_ = v_a_2281_;
goto v___jp_2074_;
}
}
else
{
lean_object* v_a_2282_; 
lean_dec(v_a_2159_);
lean_dec(v_a_2115_);
lean_dec_ref(v_s_2039_);
lean_dec_ref(v_t_2038_);
lean_dec(v_candidate_2037_);
v_a_2282_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2282_);
lean_dec_ref(v___x_2162_);
v_a_2075_ = v_a_2282_;
goto v___jp_2074_;
}
}
else
{
lean_object* v_a_2283_; 
lean_dec(v_a_2115_);
lean_dec_ref(v_s_2039_);
lean_dec_ref(v_t_2038_);
lean_dec(v_candidate_2037_);
v_a_2283_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2283_);
lean_dec_ref(v___x_2158_);
v_a_2075_ = v_a_2283_;
goto v___jp_2074_;
}
v___jp_2116_:
{
if (v_a_2117_ == 0)
{
lean_dec(v_a_2115_);
v_a_2079_ = v_a_2117_;
goto v___jp_2078_;
}
else
{
uint8_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = 0;
v___x_2119_ = l_Lean_Meta_processPostponed(v_mayPostpone_2040_, v___x_2118_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2156_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2156_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2156_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_unbox(v_a_2120_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_del_object(v___x_2122_);
lean_dec(v_a_2120_);
lean_dec(v_a_2115_);
v___x_2125_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2047_, v_a_2042_, v_a_2044_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2133_; 
lean_del_object(v___x_2049_);
lean_dec(v_a_2047_);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v___x_2125_, 0);
lean_dec(v_unused_2134_);
v___x_2127_ = v___x_2125_;
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
else
{
lean_dec(v___x_2125_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_box(v___x_2118_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2129_);
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
else
{
lean_object* v_a_2135_; 
v_a_2135_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2125_);
v_a_2075_ = v_a_2135_;
goto v___jp_2074_;
}
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v_postponed_2138_; lean_object* v_mctx_2139_; lean_object* v_cache_2140_; lean_object* v_zetaDeltaFVarIds_2141_; lean_object* v_diag_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2154_; 
lean_del_object(v___x_2049_);
lean_dec(v_a_2047_);
v___x_2136_ = lean_st_ref_get(v_a_2042_);
v___x_2137_ = lean_st_ref_take(v_a_2042_);
v_postponed_2138_ = lean_ctor_get(v___x_2136_, 3);
lean_inc_ref(v_postponed_2138_);
lean_dec(v___x_2136_);
v_mctx_2139_ = lean_ctor_get(v___x_2137_, 0);
v_cache_2140_ = lean_ctor_get(v___x_2137_, 1);
v_zetaDeltaFVarIds_2141_ = lean_ctor_get(v___x_2137_, 2);
v_diag_2142_ = lean_ctor_get(v___x_2137_, 4);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v___x_2137_, 3);
lean_dec(v_unused_2155_);
v___x_2144_ = v___x_2137_;
v_isShared_2145_ = v_isSharedCheck_2154_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_diag_2142_);
lean_inc(v_zetaDeltaFVarIds_2141_);
lean_inc(v_cache_2140_);
lean_inc(v_mctx_2139_);
lean_dec(v___x_2137_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2154_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = l_Lean_PersistentArray_append___redArg(v_a_2115_, v_postponed_2138_);
lean_dec_ref(v_postponed_2138_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 3, v___x_2146_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_mctx_2139_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_cache_2140_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_zetaDeltaFVarIds_2141_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v_diag_2142_);
v___x_2148_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_st_ref_set(v_a_2042_, v___x_2148_);
if (v_isShared_2123_ == 0)
{
v___x_2151_ = v___x_2122_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2120_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
else
{
lean_object* v_a_2157_; 
lean_dec(v_a_2115_);
v_a_2157_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2119_);
v_a_2075_ = v_a_2157_;
goto v___jp_2074_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_del_object(v___x_2049_);
lean_dec(v_a_2047_);
lean_dec_ref(v_s_2039_);
lean_dec_ref(v_t_2038_);
lean_dec(v_candidate_2037_);
v_a_2284_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2114_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2114_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
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
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_s_2039_);
lean_dec_ref(v_t_2038_);
lean_dec(v_candidate_2037_);
v_a_2298_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2046_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2046_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object* v_candidate_2306_, lean_object* v_t_2307_, lean_object* v_s_2308_, lean_object* v_mayPostpone_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
uint8_t v_mayPostpone_boxed_2315_; lean_object* v_res_2316_; 
v_mayPostpone_boxed_2315_ = lean_unbox(v_mayPostpone_2309_);
v_res_2316_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2306_, v_t_2307_, v_s_2308_, v_mayPostpone_boxed_2315_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
return v_res_2316_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = lean_unsigned_to_nat(32u);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___x_2317_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
return v___x_2319_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2320_ = ((size_t)5ULL);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_unsigned_to_nat(32u);
v___x_2323_ = lean_mk_empty_array_with_capacity(v___x_2322_);
v___x_2324_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0);
v___x_2325_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v___x_2323_);
lean_ctor_set(v___x_2325_, 2, v___x_2321_);
lean_ctor_set(v___x_2325_, 3, v___x_2321_);
lean_ctor_set_usize(v___x_2325_, 4, v___x_2320_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; lean_object* v_traceState_2329_; lean_object* v_traces_2330_; lean_object* v___x_2331_; lean_object* v_traceState_2332_; lean_object* v_env_2333_; lean_object* v_nextMacroScope_2334_; lean_object* v_ngen_2335_; lean_object* v_auxDeclNGen_2336_; lean_object* v_cache_2337_; lean_object* v_messages_2338_; lean_object* v_infoState_2339_; lean_object* v_snapshotTasks_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2359_; 
v___x_2328_ = lean_st_ref_get(v___y_2326_);
v_traceState_2329_ = lean_ctor_get(v___x_2328_, 4);
lean_inc_ref(v_traceState_2329_);
lean_dec(v___x_2328_);
v_traces_2330_ = lean_ctor_get(v_traceState_2329_, 0);
lean_inc_ref(v_traces_2330_);
lean_dec_ref(v_traceState_2329_);
v___x_2331_ = lean_st_ref_take(v___y_2326_);
v_traceState_2332_ = lean_ctor_get(v___x_2331_, 4);
v_env_2333_ = lean_ctor_get(v___x_2331_, 0);
v_nextMacroScope_2334_ = lean_ctor_get(v___x_2331_, 1);
v_ngen_2335_ = lean_ctor_get(v___x_2331_, 2);
v_auxDeclNGen_2336_ = lean_ctor_get(v___x_2331_, 3);
v_cache_2337_ = lean_ctor_get(v___x_2331_, 5);
v_messages_2338_ = lean_ctor_get(v___x_2331_, 6);
v_infoState_2339_ = lean_ctor_get(v___x_2331_, 7);
v_snapshotTasks_2340_ = lean_ctor_get(v___x_2331_, 8);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2342_ = v___x_2331_;
v_isShared_2343_ = v_isSharedCheck_2359_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_snapshotTasks_2340_);
lean_inc(v_infoState_2339_);
lean_inc(v_messages_2338_);
lean_inc(v_cache_2337_);
lean_inc(v_traceState_2332_);
lean_inc(v_auxDeclNGen_2336_);
lean_inc(v_ngen_2335_);
lean_inc(v_nextMacroScope_2334_);
lean_inc(v_env_2333_);
lean_dec(v___x_2331_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2359_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
uint64_t v_tid_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2357_; 
v_tid_2344_ = lean_ctor_get_uint64(v_traceState_2332_, sizeof(void*)*1);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_traceState_2332_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; 
v_unused_2358_ = lean_ctor_get(v_traceState_2332_, 0);
lean_dec(v_unused_2358_);
v___x_2346_ = v_traceState_2332_;
v_isShared_2347_ = v_isSharedCheck_2357_;
goto v_resetjp_2345_;
}
else
{
lean_dec(v_traceState_2332_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2357_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2350_ = v___x_2346_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2348_);
lean_ctor_set_uint64(v_reuseFailAlloc_2356_, sizeof(void*)*1, v_tid_2344_);
v___x_2350_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2352_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 4, v___x_2350_);
v___x_2352_ = v___x_2342_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_env_2333_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_nextMacroScope_2334_);
lean_ctor_set(v_reuseFailAlloc_2355_, 2, v_ngen_2335_);
lean_ctor_set(v_reuseFailAlloc_2355_, 3, v_auxDeclNGen_2336_);
lean_ctor_set(v_reuseFailAlloc_2355_, 4, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2355_, 5, v_cache_2337_);
lean_ctor_set(v_reuseFailAlloc_2355_, 6, v_messages_2338_);
lean_ctor_set(v_reuseFailAlloc_2355_, 7, v_infoState_2339_);
lean_ctor_set(v_reuseFailAlloc_2355_, 8, v_snapshotTasks_2340_);
v___x_2352_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_st_ref_set(v___y_2326_, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_traces_2330_);
return v___x_2354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___boxed(lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2360_);
lean_dec(v___y_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
return v_res_2374_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object* v_opts_2375_, lean_object* v_opt_2376_){
_start:
{
lean_object* v_name_2377_; lean_object* v_defValue_2378_; lean_object* v_map_2379_; lean_object* v___x_2380_; 
v_name_2377_ = lean_ctor_get(v_opt_2376_, 0);
v_defValue_2378_ = lean_ctor_get(v_opt_2376_, 1);
v_map_2379_ = lean_ctor_get(v_opts_2375_, 0);
v___x_2380_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2379_, v_name_2377_);
if (lean_obj_tag(v___x_2380_) == 0)
{
uint8_t v___x_2381_; 
v___x_2381_ = lean_unbox(v_defValue_2378_);
return v___x_2381_;
}
else
{
lean_object* v_val_2382_; 
v_val_2382_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_val_2382_);
lean_dec_ref(v___x_2380_);
if (lean_obj_tag(v_val_2382_) == 1)
{
uint8_t v_v_2383_; 
v_v_2383_ = lean_ctor_get_uint8(v_val_2382_, 0);
lean_dec_ref(v_val_2382_);
return v_v_2383_;
}
else
{
uint8_t v___x_2384_; 
lean_dec(v_val_2382_);
v___x_2384_ = lean_unbox(v_defValue_2378_);
return v___x_2384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object* v_opts_2385_, lean_object* v_opt_2386_){
_start:
{
uint8_t v_res_2387_; lean_object* v_r_2388_; 
v_res_2387_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2385_, v_opt_2386_);
lean_dec_ref(v_opt_2386_);
lean_dec_ref(v_opts_2385_);
v_r_2388_ = lean_box(v_res_2387_);
return v_r_2388_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4));
v___x_2397_ = l_Lean_stringToMessageData(v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object* v_candidate_2398_, lean_object* v_t_2399_, lean_object* v_s_2400_, lean_object* v_x_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2407_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1);
v___x_2408_ = l_Lean_MessageData_ofName(v_candidate_2398_);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = l_Lean_MessageData_ofExpr(v_t_2399_);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = l_Lean_MessageData_ofExpr(v_s_2400_);
v___x_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object* v_candidate_2419_, lean_object* v_t_2420_, lean_object* v_s_2421_, lean_object* v_x_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(v_candidate_2419_, v_t_2420_, v_s_2421_, v_x_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec_ref(v_x_2422_);
return v_res_2428_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(lean_object* v_e_2429_){
_start:
{
if (lean_obj_tag(v_e_2429_) == 0)
{
uint8_t v___x_2430_; 
v___x_2430_ = 2;
return v___x_2430_;
}
else
{
lean_object* v_a_2431_; uint8_t v___x_2432_; 
v_a_2431_ = lean_ctor_get(v_e_2429_, 0);
v___x_2432_ = lean_unbox(v_a_2431_);
if (v___x_2432_ == 0)
{
uint8_t v___x_2433_; 
v___x_2433_ = 1;
return v___x_2433_;
}
else
{
uint8_t v___x_2434_; 
v___x_2434_ = 0;
return v___x_2434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(lean_object* v_e_2435_){
_start:
{
uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_res_2436_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_e_2435_);
lean_dec_ref(v_e_2435_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(lean_object* v_opts_2438_, lean_object* v_opt_2439_){
_start:
{
lean_object* v_name_2440_; lean_object* v_defValue_2441_; lean_object* v_map_2442_; lean_object* v___x_2443_; 
v_name_2440_ = lean_ctor_get(v_opt_2439_, 0);
v_defValue_2441_ = lean_ctor_get(v_opt_2439_, 1);
v_map_2442_ = lean_ctor_get(v_opts_2438_, 0);
v___x_2443_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2442_, v_name_2440_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_inc(v_defValue_2441_);
return v_defValue_2441_;
}
else
{
lean_object* v_val_2444_; 
v_val_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_val_2444_);
lean_dec_ref(v___x_2443_);
if (lean_obj_tag(v_val_2444_) == 3)
{
lean_object* v_v_2445_; 
v_v_2445_ = lean_ctor_get(v_val_2444_, 0);
lean_inc(v_v_2445_);
lean_dec_ref(v_val_2444_);
return v_v_2445_;
}
else
{
lean_dec(v_val_2444_);
lean_inc(v_defValue_2441_);
return v_defValue_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(lean_object* v_opts_2446_, lean_object* v_opt_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2446_, v_opt_2447_);
lean_dec_ref(v_opt_2447_);
lean_dec_ref(v_opts_2446_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(lean_object* v_x_2449_){
_start:
{
if (lean_obj_tag(v_x_2449_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_a_2451_ = lean_ctor_get(v_x_2449_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_x_2449_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v_x_2449_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v_x_2449_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set_tag(v___x_2453_, 1);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v_a_2459_ = lean_ctor_get(v_x_2449_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_x_2449_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v_x_2449_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v_x_2449_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set_tag(v___x_2461_, 0);
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg___boxed(lean_object* v_x_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_x_2467_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(size_t v_sz_2470_, size_t v_i_2471_, lean_object* v_bs_2472_){
_start:
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_usize_dec_lt(v_i_2471_, v_sz_2470_);
if (v___x_2473_ == 0)
{
return v_bs_2472_;
}
else
{
lean_object* v_v_2474_; lean_object* v_msg_2475_; lean_object* v___x_2476_; lean_object* v_bs_x27_2477_; size_t v___x_2478_; size_t v___x_2479_; lean_object* v___x_2480_; 
v_v_2474_ = lean_array_uget_borrowed(v_bs_2472_, v_i_2471_);
v_msg_2475_ = lean_ctor_get(v_v_2474_, 1);
lean_inc_ref(v_msg_2475_);
v___x_2476_ = lean_unsigned_to_nat(0u);
v_bs_x27_2477_ = lean_array_uset(v_bs_2472_, v_i_2471_, v___x_2476_);
v___x_2478_ = ((size_t)1ULL);
v___x_2479_ = lean_usize_add(v_i_2471_, v___x_2478_);
v___x_2480_ = lean_array_uset(v_bs_x27_2477_, v_i_2471_, v_msg_2475_);
v_i_2471_ = v___x_2479_;
v_bs_2472_ = v___x_2480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9___boxed(lean_object* v_sz_2482_, lean_object* v_i_2483_, lean_object* v_bs_2484_){
_start:
{
size_t v_sz_boxed_2485_; size_t v_i_boxed_2486_; lean_object* v_res_2487_; 
v_sz_boxed_2485_ = lean_unbox_usize(v_sz_2482_);
lean_dec(v_sz_2482_);
v_i_boxed_2486_ = lean_unbox_usize(v_i_2483_);
lean_dec(v_i_2483_);
v_res_2487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(v_sz_boxed_2485_, v_i_boxed_2486_, v_bs_2484_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(lean_object* v_oldTraces_2488_, lean_object* v_data_2489_, lean_object* v_ref_2490_, lean_object* v_msg_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_fileName_2497_; lean_object* v_fileMap_2498_; lean_object* v_options_2499_; lean_object* v_currRecDepth_2500_; lean_object* v_maxRecDepth_2501_; lean_object* v_ref_2502_; lean_object* v_currNamespace_2503_; lean_object* v_openDecls_2504_; lean_object* v_initHeartbeats_2505_; lean_object* v_maxHeartbeats_2506_; lean_object* v_quotContext_2507_; lean_object* v_currMacroScope_2508_; uint8_t v_diag_2509_; lean_object* v_cancelTk_x3f_2510_; uint8_t v_suppressElabErrors_2511_; lean_object* v_inheritedTraceOptions_2512_; lean_object* v___x_2513_; lean_object* v_traceState_2514_; lean_object* v_traces_2515_; lean_object* v_ref_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; size_t v_sz_2519_; size_t v___x_2520_; lean_object* v___x_2521_; lean_object* v_msg_2522_; lean_object* v___x_2523_; lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2561_; 
v_fileName_2497_ = lean_ctor_get(v___y_2494_, 0);
v_fileMap_2498_ = lean_ctor_get(v___y_2494_, 1);
v_options_2499_ = lean_ctor_get(v___y_2494_, 2);
v_currRecDepth_2500_ = lean_ctor_get(v___y_2494_, 3);
v_maxRecDepth_2501_ = lean_ctor_get(v___y_2494_, 4);
v_ref_2502_ = lean_ctor_get(v___y_2494_, 5);
v_currNamespace_2503_ = lean_ctor_get(v___y_2494_, 6);
v_openDecls_2504_ = lean_ctor_get(v___y_2494_, 7);
v_initHeartbeats_2505_ = lean_ctor_get(v___y_2494_, 8);
v_maxHeartbeats_2506_ = lean_ctor_get(v___y_2494_, 9);
v_quotContext_2507_ = lean_ctor_get(v___y_2494_, 10);
v_currMacroScope_2508_ = lean_ctor_get(v___y_2494_, 11);
v_diag_2509_ = lean_ctor_get_uint8(v___y_2494_, sizeof(void*)*14);
v_cancelTk_x3f_2510_ = lean_ctor_get(v___y_2494_, 12);
v_suppressElabErrors_2511_ = lean_ctor_get_uint8(v___y_2494_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2512_ = lean_ctor_get(v___y_2494_, 13);
v___x_2513_ = lean_st_ref_get(v___y_2495_);
v_traceState_2514_ = lean_ctor_get(v___x_2513_, 4);
lean_inc_ref(v_traceState_2514_);
lean_dec(v___x_2513_);
v_traces_2515_ = lean_ctor_get(v_traceState_2514_, 0);
lean_inc_ref(v_traces_2515_);
lean_dec_ref(v_traceState_2514_);
v_ref_2516_ = l_Lean_replaceRef(v_ref_2490_, v_ref_2502_);
lean_inc_ref(v_inheritedTraceOptions_2512_);
lean_inc(v_cancelTk_x3f_2510_);
lean_inc(v_currMacroScope_2508_);
lean_inc(v_quotContext_2507_);
lean_inc(v_maxHeartbeats_2506_);
lean_inc(v_initHeartbeats_2505_);
lean_inc(v_openDecls_2504_);
lean_inc(v_currNamespace_2503_);
lean_inc(v_maxRecDepth_2501_);
lean_inc(v_currRecDepth_2500_);
lean_inc_ref(v_options_2499_);
lean_inc_ref(v_fileMap_2498_);
lean_inc_ref(v_fileName_2497_);
v___x_2517_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2517_, 0, v_fileName_2497_);
lean_ctor_set(v___x_2517_, 1, v_fileMap_2498_);
lean_ctor_set(v___x_2517_, 2, v_options_2499_);
lean_ctor_set(v___x_2517_, 3, v_currRecDepth_2500_);
lean_ctor_set(v___x_2517_, 4, v_maxRecDepth_2501_);
lean_ctor_set(v___x_2517_, 5, v_ref_2516_);
lean_ctor_set(v___x_2517_, 6, v_currNamespace_2503_);
lean_ctor_set(v___x_2517_, 7, v_openDecls_2504_);
lean_ctor_set(v___x_2517_, 8, v_initHeartbeats_2505_);
lean_ctor_set(v___x_2517_, 9, v_maxHeartbeats_2506_);
lean_ctor_set(v___x_2517_, 10, v_quotContext_2507_);
lean_ctor_set(v___x_2517_, 11, v_currMacroScope_2508_);
lean_ctor_set(v___x_2517_, 12, v_cancelTk_x3f_2510_);
lean_ctor_set(v___x_2517_, 13, v_inheritedTraceOptions_2512_);
lean_ctor_set_uint8(v___x_2517_, sizeof(void*)*14, v_diag_2509_);
lean_ctor_set_uint8(v___x_2517_, sizeof(void*)*14 + 1, v_suppressElabErrors_2511_);
v___x_2518_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2515_);
lean_dec_ref(v_traces_2515_);
v_sz_2519_ = lean_array_size(v___x_2518_);
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(v_sz_2519_, v___x_2520_, v___x_2518_);
v_msg_2522_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2522_, 0, v_data_2489_);
lean_ctor_set(v_msg_2522_, 1, v_msg_2491_);
lean_ctor_set(v_msg_2522_, 2, v___x_2521_);
v___x_2523_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2522_, v___y_2492_, v___y_2493_, v___x_2517_, v___y_2495_);
lean_dec_ref(v___x_2517_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2561_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2561_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v_traceState_2529_; lean_object* v_env_2530_; lean_object* v_nextMacroScope_2531_; lean_object* v_ngen_2532_; lean_object* v_auxDeclNGen_2533_; lean_object* v_cache_2534_; lean_object* v_messages_2535_; lean_object* v_infoState_2536_; lean_object* v_snapshotTasks_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2560_; 
v___x_2528_ = lean_st_ref_take(v___y_2495_);
v_traceState_2529_ = lean_ctor_get(v___x_2528_, 4);
v_env_2530_ = lean_ctor_get(v___x_2528_, 0);
v_nextMacroScope_2531_ = lean_ctor_get(v___x_2528_, 1);
v_ngen_2532_ = lean_ctor_get(v___x_2528_, 2);
v_auxDeclNGen_2533_ = lean_ctor_get(v___x_2528_, 3);
v_cache_2534_ = lean_ctor_get(v___x_2528_, 5);
v_messages_2535_ = lean_ctor_get(v___x_2528_, 6);
v_infoState_2536_ = lean_ctor_get(v___x_2528_, 7);
v_snapshotTasks_2537_ = lean_ctor_get(v___x_2528_, 8);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2539_ = v___x_2528_;
v_isShared_2540_ = v_isSharedCheck_2560_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_snapshotTasks_2537_);
lean_inc(v_infoState_2536_);
lean_inc(v_messages_2535_);
lean_inc(v_cache_2534_);
lean_inc(v_traceState_2529_);
lean_inc(v_auxDeclNGen_2533_);
lean_inc(v_ngen_2532_);
lean_inc(v_nextMacroScope_2531_);
lean_inc(v_env_2530_);
lean_dec(v___x_2528_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2560_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
uint64_t v_tid_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2558_; 
v_tid_2541_ = lean_ctor_get_uint64(v_traceState_2529_, sizeof(void*)*1);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_traceState_2529_);
if (v_isSharedCheck_2558_ == 0)
{
lean_object* v_unused_2559_; 
v_unused_2559_ = lean_ctor_get(v_traceState_2529_, 0);
lean_dec(v_unused_2559_);
v___x_2543_ = v_traceState_2529_;
v_isShared_2544_ = v_isSharedCheck_2558_;
goto v_resetjp_2542_;
}
else
{
lean_dec(v_traceState_2529_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2558_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2545_, 0, v_ref_2490_);
lean_ctor_set(v___x_2545_, 1, v_a_2524_);
v___x_2546_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2488_, v___x_2545_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2546_);
v___x_2548_ = v___x_2543_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2546_);
lean_ctor_set_uint64(v_reuseFailAlloc_2557_, sizeof(void*)*1, v_tid_2541_);
v___x_2548_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2550_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 4, v___x_2548_);
v___x_2550_ = v___x_2539_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_env_2530_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_nextMacroScope_2531_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_ngen_2532_);
lean_ctor_set(v_reuseFailAlloc_2556_, 3, v_auxDeclNGen_2533_);
lean_ctor_set(v_reuseFailAlloc_2556_, 4, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2556_, 5, v_cache_2534_);
lean_ctor_set(v_reuseFailAlloc_2556_, 6, v_messages_2535_);
lean_ctor_set(v_reuseFailAlloc_2556_, 7, v_infoState_2536_);
lean_ctor_set(v_reuseFailAlloc_2556_, 8, v_snapshotTasks_2537_);
v___x_2550_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2551_ = lean_st_ref_set(v___y_2495_, v___x_2550_);
v___x_2552_ = lean_box(0);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2552_);
v___x_2554_ = v___x_2526_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(lean_object* v_oldTraces_2562_, lean_object* v_data_2563_, lean_object* v_ref_2564_, lean_object* v_msg_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_oldTraces_2562_, v_data_2563_, v_ref_2564_, v_msg_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
return v_res_2571_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0));
v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
return v___x_2574_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2));
v___x_2577_ = l_Lean_stringToMessageData(v___x_2576_);
return v___x_2577_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4(void){
_start:
{
lean_object* v___x_2578_; double v___x_2579_; 
v___x_2578_ = lean_unsigned_to_nat(1000u);
v___x_2579_ = lean_float_of_nat(v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object* v_cls_2580_, uint8_t v_collapsed_2581_, lean_object* v_tag_2582_, lean_object* v_opts_2583_, uint8_t v_clsEnabled_2584_, lean_object* v_oldTraces_2585_, lean_object* v_msg_2586_, lean_object* v_resStartStop_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_fst_2593_; lean_object* v_snd_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2692_; 
v_fst_2593_ = lean_ctor_get(v_resStartStop_2587_, 0);
v_snd_2594_ = lean_ctor_get(v_resStartStop_2587_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_resStartStop_2587_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2596_ = v_resStartStop_2587_;
v_isShared_2597_ = v_isSharedCheck_2692_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_snd_2594_);
lean_inc(v_fst_2593_);
lean_dec(v_resStartStop_2587_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2692_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v_data_2601_; lean_object* v_fst_2612_; lean_object* v_snd_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2691_; 
v_fst_2612_ = lean_ctor_get(v_snd_2594_, 0);
v_snd_2613_ = lean_ctor_get(v_snd_2594_, 1);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_snd_2594_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2615_ = v_snd_2594_;
v_isShared_2616_ = v_isSharedCheck_2691_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_snd_2613_);
lean_inc(v_fst_2612_);
lean_dec(v_snd_2594_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2691_;
goto v_resetjp_2614_;
}
v___jp_2598_:
{
lean_object* v___x_2602_; 
lean_inc(v___y_2599_);
v___x_2602_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_oldTraces_2585_, v_data_2601_, v___y_2599_, v___y_2600_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v___x_2603_; 
lean_dec_ref(v___x_2602_);
v___x_2603_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_fst_2593_);
return v___x_2603_;
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_fst_2593_);
v_a_2604_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2602_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2602_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
v_resetjp_2614_:
{
lean_object* v___x_2617_; uint8_t v___x_2618_; lean_object* v___y_2620_; lean_object* v_a_2621_; uint8_t v___y_2645_; double v___y_2676_; 
v___x_2617_ = l_Lean_trace_profiler;
v___x_2618_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2583_, v___x_2617_);
if (v___x_2618_ == 0)
{
v___y_2645_ = v___x_2618_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2682_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2583_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; double v___x_2685_; double v___x_2686_; double v___x_2687_; 
v___x_2683_ = l_Lean_trace_profiler_threshold;
v___x_2684_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2583_, v___x_2683_);
v___x_2685_ = lean_float_of_nat(v___x_2684_);
v___x_2686_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4);
v___x_2687_ = lean_float_div(v___x_2685_, v___x_2686_);
v___y_2676_ = v___x_2687_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; double v___x_2690_; 
v___x_2688_ = l_Lean_trace_profiler_threshold;
v___x_2689_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2583_, v___x_2688_);
v___x_2690_ = lean_float_of_nat(v___x_2689_);
v___y_2676_ = v___x_2690_;
goto v___jp_2675_;
}
}
v___jp_2619_:
{
uint8_t v_result_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v_result_2622_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_fst_2593_);
v___x_2623_ = l_Lean_TraceResult_toEmoji(v_result_2622_);
v___x_2624_ = l_Lean_stringToMessageData(v___x_2623_);
v___x_2625_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1);
if (v_isShared_2616_ == 0)
{
lean_ctor_set_tag(v___x_2615_, 7);
lean_ctor_set(v___x_2615_, 1, v___x_2625_);
lean_ctor_set(v___x_2615_, 0, v___x_2624_);
v___x_2627_ = v___x_2615_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v_m_2629_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set_tag(v___x_2596_, 7);
lean_ctor_set(v___x_2596_, 1, v_a_2621_);
lean_ctor_set(v___x_2596_, 0, v___x_2627_);
v_m_2629_ = v___x_2596_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_a_2621_);
v_m_2629_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; double v___x_2632_; lean_object* v_data_2633_; 
v___x_2630_ = lean_box(v_result_2622_);
v___x_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
v___x_2632_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
lean_inc_ref(v_tag_2582_);
lean_inc_ref(v___x_2631_);
lean_inc(v_cls_2580_);
v_data_2633_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2633_, 0, v_cls_2580_);
lean_ctor_set(v_data_2633_, 1, v___x_2631_);
lean_ctor_set(v_data_2633_, 2, v_tag_2582_);
lean_ctor_set_float(v_data_2633_, sizeof(void*)*3, v___x_2632_);
lean_ctor_set_float(v_data_2633_, sizeof(void*)*3 + 8, v___x_2632_);
lean_ctor_set_uint8(v_data_2633_, sizeof(void*)*3 + 16, v_collapsed_2581_);
if (v___x_2618_ == 0)
{
lean_dec_ref(v___x_2631_);
lean_dec(v_snd_2613_);
lean_dec(v_fst_2612_);
lean_dec_ref(v_tag_2582_);
lean_dec(v_cls_2580_);
v___y_2599_ = v___y_2620_;
v___y_2600_ = v_m_2629_;
v_data_2601_ = v_data_2633_;
goto v___jp_2598_;
}
else
{
lean_object* v_data_2634_; double v___x_2635_; double v___x_2636_; 
lean_dec_ref(v_data_2633_);
v_data_2634_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2634_, 0, v_cls_2580_);
lean_ctor_set(v_data_2634_, 1, v___x_2631_);
lean_ctor_set(v_data_2634_, 2, v_tag_2582_);
v___x_2635_ = lean_unbox_float(v_fst_2612_);
lean_dec(v_fst_2612_);
lean_ctor_set_float(v_data_2634_, sizeof(void*)*3, v___x_2635_);
v___x_2636_ = lean_unbox_float(v_snd_2613_);
lean_dec(v_snd_2613_);
lean_ctor_set_float(v_data_2634_, sizeof(void*)*3 + 8, v___x_2636_);
lean_ctor_set_uint8(v_data_2634_, sizeof(void*)*3 + 16, v_collapsed_2581_);
v___y_2599_ = v___y_2620_;
v___y_2600_ = v_m_2629_;
v_data_2601_ = v_data_2634_;
goto v___jp_2598_;
}
}
}
}
v___jp_2639_:
{
lean_object* v_ref_2640_; lean_object* v___x_2641_; 
v_ref_2640_ = lean_ctor_get(v___y_2590_, 5);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v_fst_2593_);
v___x_2641_ = lean_apply_6(v_msg_2586_, v_fst_2593_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref(v___x_2641_);
v___y_2620_ = v_ref_2640_;
v_a_2621_ = v_a_2642_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2643_; 
lean_dec_ref(v___x_2641_);
v___x_2643_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3);
v___y_2620_ = v_ref_2640_;
v_a_2621_ = v___x_2643_;
goto v___jp_2619_;
}
}
v___jp_2644_:
{
if (v_clsEnabled_2584_ == 0)
{
if (v___y_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v_traceState_2647_; lean_object* v_env_2648_; lean_object* v_nextMacroScope_2649_; lean_object* v_ngen_2650_; lean_object* v_auxDeclNGen_2651_; lean_object* v_cache_2652_; lean_object* v_messages_2653_; lean_object* v_infoState_2654_; lean_object* v_snapshotTasks_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2674_; 
lean_del_object(v___x_2615_);
lean_dec(v_snd_2613_);
lean_dec(v_fst_2612_);
lean_del_object(v___x_2596_);
lean_dec_ref(v_msg_2586_);
lean_dec_ref(v_tag_2582_);
lean_dec(v_cls_2580_);
v___x_2646_ = lean_st_ref_take(v___y_2591_);
v_traceState_2647_ = lean_ctor_get(v___x_2646_, 4);
v_env_2648_ = lean_ctor_get(v___x_2646_, 0);
v_nextMacroScope_2649_ = lean_ctor_get(v___x_2646_, 1);
v_ngen_2650_ = lean_ctor_get(v___x_2646_, 2);
v_auxDeclNGen_2651_ = lean_ctor_get(v___x_2646_, 3);
v_cache_2652_ = lean_ctor_get(v___x_2646_, 5);
v_messages_2653_ = lean_ctor_get(v___x_2646_, 6);
v_infoState_2654_ = lean_ctor_get(v___x_2646_, 7);
v_snapshotTasks_2655_ = lean_ctor_get(v___x_2646_, 8);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2657_ = v___x_2646_;
v_isShared_2658_ = v_isSharedCheck_2674_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snapshotTasks_2655_);
lean_inc(v_infoState_2654_);
lean_inc(v_messages_2653_);
lean_inc(v_cache_2652_);
lean_inc(v_traceState_2647_);
lean_inc(v_auxDeclNGen_2651_);
lean_inc(v_ngen_2650_);
lean_inc(v_nextMacroScope_2649_);
lean_inc(v_env_2648_);
lean_dec(v___x_2646_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2674_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
uint64_t v_tid_2659_; lean_object* v_traces_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2673_; 
v_tid_2659_ = lean_ctor_get_uint64(v_traceState_2647_, sizeof(void*)*1);
v_traces_2660_ = lean_ctor_get(v_traceState_2647_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_traceState_2647_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2662_ = v_traceState_2647_;
v_isShared_2663_ = v_isSharedCheck_2673_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_traces_2660_);
lean_dec(v_traceState_2647_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2673_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2664_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2585_, v_traces_2660_);
lean_dec_ref(v_traces_2660_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2664_);
v___x_2666_ = v___x_2662_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2664_);
lean_ctor_set_uint64(v_reuseFailAlloc_2672_, sizeof(void*)*1, v_tid_2659_);
v___x_2666_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2668_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 4, v___x_2666_);
v___x_2668_ = v___x_2657_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_env_2648_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_nextMacroScope_2649_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_ngen_2650_);
lean_ctor_set(v_reuseFailAlloc_2671_, 3, v_auxDeclNGen_2651_);
lean_ctor_set(v_reuseFailAlloc_2671_, 4, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2671_, 5, v_cache_2652_);
lean_ctor_set(v_reuseFailAlloc_2671_, 6, v_messages_2653_);
lean_ctor_set(v_reuseFailAlloc_2671_, 7, v_infoState_2654_);
lean_ctor_set(v_reuseFailAlloc_2671_, 8, v_snapshotTasks_2655_);
v___x_2668_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_st_ref_set(v___y_2591_, v___x_2668_);
v___x_2670_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_fst_2593_);
return v___x_2670_;
}
}
}
}
}
else
{
goto v___jp_2639_;
}
}
else
{
goto v___jp_2639_;
}
}
v___jp_2675_:
{
double v___x_2677_; double v___x_2678_; double v___x_2679_; uint8_t v___x_2680_; 
v___x_2677_ = lean_unbox_float(v_snd_2613_);
v___x_2678_ = lean_unbox_float(v_fst_2612_);
v___x_2679_ = lean_float_sub(v___x_2677_, v___x_2678_);
v___x_2680_ = lean_float_decLt(v___y_2676_, v___x_2679_);
v___y_2645_ = v___x_2680_;
goto v___jp_2644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object* v_cls_2693_, lean_object* v_collapsed_2694_, lean_object* v_tag_2695_, lean_object* v_opts_2696_, lean_object* v_clsEnabled_2697_, lean_object* v_oldTraces_2698_, lean_object* v_msg_2699_, lean_object* v_resStartStop_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
uint8_t v_collapsed_boxed_2706_; uint8_t v_clsEnabled_boxed_2707_; lean_object* v_res_2708_; 
v_collapsed_boxed_2706_ = lean_unbox(v_collapsed_2694_);
v_clsEnabled_boxed_2707_ = lean_unbox(v_clsEnabled_2697_);
v_res_2708_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2693_, v_collapsed_boxed_2706_, v_tag_2695_, v_opts_2696_, v_clsEnabled_boxed_2707_, v_oldTraces_2698_, v_msg_2699_, v_resStartStop_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec_ref(v_opts_2696_);
return v_res_2708_;
}
}
static double _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0(void){
_start:
{
lean_object* v___x_2709_; double v___x_2710_; 
v___x_2709_ = lean_unsigned_to_nat(1000000000u);
v___x_2710_ = lean_float_of_nat(v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object* v_t_2711_, lean_object* v_s_2712_, lean_object* v_candidate_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_options_2719_; lean_object* v_inheritedTraceOptions_2720_; uint8_t v_hasTrace_2721_; uint8_t v___x_2722_; 
v_options_2719_ = lean_ctor_get(v_a_2716_, 2);
v_inheritedTraceOptions_2720_ = lean_ctor_get(v_a_2716_, 13);
v_hasTrace_2721_ = lean_ctor_get_uint8(v_options_2719_, sizeof(void*)*1);
v___x_2722_ = 1;
if (v_hasTrace_2721_ == 0)
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2713_, v_t_2711_, v_s_2712_, v___x_2722_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
return v___x_2723_;
}
else
{
lean_object* v___f_2724_; lean_object* v_cls_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v_a_2732_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v_a_2747_; 
lean_inc_ref(v_s_2712_);
lean_inc_ref(v_t_2711_);
lean_inc(v_candidate_2713_);
v___f_2724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2724_, 0, v_candidate_2713_);
lean_closure_set(v___f_2724_, 1, v_t_2711_);
lean_closure_set(v___f_2724_, 2, v_s_2712_);
v_cls_2725_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2726_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_2727_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2720_, v_options_2719_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2797_ = l_Lean_trace_profiler;
v___x_2798_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2719_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; 
lean_dec_ref(v___f_2724_);
v___x_2799_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2713_, v_t_2711_, v_s_2712_, v___x_2722_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
return v___x_2799_;
}
else
{
goto v___jp_2756_;
}
}
else
{
goto v___jp_2756_;
}
v___jp_2729_:
{
lean_object* v___x_2733_; double v___x_2734_; double v___x_2735_; double v___x_2736_; double v___x_2737_; double v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2733_ = lean_io_mono_nanos_now();
v___x_2734_ = lean_float_of_nat(v___y_2730_);
v___x_2735_ = lean_float_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0);
v___x_2736_ = lean_float_div(v___x_2734_, v___x_2735_);
v___x_2737_ = lean_float_of_nat(v___x_2733_);
v___x_2738_ = lean_float_div(v___x_2737_, v___x_2735_);
v___x_2739_ = lean_box_float(v___x_2736_);
v___x_2740_ = lean_box_float(v___x_2738_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v_a_2732_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2725_, v___x_2722_, v___x_2726_, v_options_2719_, v___x_2728_, v___y_2731_, v___f_2724_, v___x_2742_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
return v___x_2743_;
}
v___jp_2744_:
{
lean_object* v___x_2748_; double v___x_2749_; double v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2748_ = lean_io_get_num_heartbeats();
v___x_2749_ = lean_float_of_nat(v___y_2746_);
v___x_2750_ = lean_float_of_nat(v___x_2748_);
v___x_2751_ = lean_box_float(v___x_2749_);
v___x_2752_ = lean_box_float(v___x_2750_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_a_2747_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2725_, v___x_2722_, v___x_2726_, v_options_2719_, v___x_2728_, v___y_2745_, v___f_2724_, v___x_2754_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
return v___x_2755_;
}
v___jp_2756_:
{
lean_object* v___x_2757_; lean_object* v_a_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2757_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v_a_2717_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref(v___x_2757_);
v___x_2759_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2760_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2719_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = lean_io_mono_nanos_now();
v___x_2762_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2713_, v_t_2711_, v_s_2712_, v___x_2722_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set_tag(v___x_2765_, 1);
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
v___y_2730_ = v___x_2761_;
v___y_2731_ = v_a_2758_;
v_a_2732_ = v___x_2768_;
goto v___jp_2729_;
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
v_a_2771_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2762_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2762_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 0);
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
v___y_2730_ = v___x_2761_;
v___y_2731_ = v_a_2758_;
v_a_2732_ = v___x_2776_;
goto v___jp_2729_;
}
}
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_io_get_num_heartbeats();
v___x_2780_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2713_, v_t_2711_, v_s_2712_, v___x_2722_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set_tag(v___x_2783_, 1);
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
v___y_2745_ = v_a_2758_;
v___y_2746_ = v___x_2779_;
v_a_2747_ = v___x_2786_;
goto v___jp_2744_;
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_a_2789_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2780_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2780_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 0);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
v___y_2745_ = v_a_2758_;
v___y_2746_ = v___x_2779_;
v_a_2747_ = v___x_2794_;
goto v___jp_2744_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object* v_t_2800_, lean_object* v_s_2801_, lean_object* v_candidate_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2800_, v_s_2801_, v_candidate_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object* v_as_2809_, lean_object* v_as_x27_2810_, lean_object* v_b_2811_, lean_object* v_a_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2810_, v_b_2811_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object* v_as_2819_, lean_object* v_as_x27_2820_, lean_object* v_b_2821_, lean_object* v_a_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(v_as_2819_, v_as_x27_2820_, v_b_2821_, v_a_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v_as_2819_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(lean_object* v_00_u03b1_2829_, lean_object* v_x_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_x_2830_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_x_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_00_u03b1_2837_, v_x_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(lean_object* v_t_2845_, lean_object* v_s_2846_, uint8_t v___x_2847_, lean_object* v_as_2848_, size_t v_sz_2849_, size_t v_i_2850_, lean_object* v_b_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
uint8_t v___x_2857_; 
v___x_2857_ = lean_usize_dec_lt(v_i_2850_, v_sz_2849_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
lean_dec_ref(v_s_2846_);
lean_dec_ref(v_t_2845_);
v___x_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2858_, 0, v_b_2851_);
return v___x_2858_;
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
lean_dec_ref(v_b_2851_);
v_a_2859_ = lean_array_uget_borrowed(v_as_2848_, v_i_2850_);
lean_inc(v_a_2859_);
lean_inc_ref(v_s_2846_);
lean_inc_ref(v_t_2845_);
v___x_2860_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2845_, v_s_2846_, v_a_2859_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2877_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2877_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2877_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = lean_box(0);
v___x_2866_ = lean_unbox(v_a_2861_);
lean_dec(v_a_2861_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; size_t v___x_2868_; size_t v___x_2869_; 
lean_del_object(v___x_2863_);
v___x_2867_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v___x_2868_ = ((size_t)1ULL);
v___x_2869_ = lean_usize_add(v_i_2850_, v___x_2868_);
v_i_2850_ = v___x_2869_;
v_b_2851_ = v___x_2867_;
goto _start;
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
lean_dec_ref(v_s_2846_);
lean_dec_ref(v_t_2845_);
v___x_2871_ = lean_box(v___x_2847_);
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v___x_2865_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2873_);
v___x_2875_ = v___x_2863_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec_ref(v_s_2846_);
lean_dec_ref(v_t_2845_);
v_a_2878_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2860_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2860_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object* v_t_2886_, lean_object* v_s_2887_, lean_object* v___x_2888_, lean_object* v_as_2889_, lean_object* v_sz_2890_, lean_object* v_i_2891_, lean_object* v_b_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
uint8_t v___x_3585__boxed_2898_; size_t v_sz_boxed_2899_; size_t v_i_boxed_2900_; lean_object* v_res_2901_; 
v___x_3585__boxed_2898_ = lean_unbox(v___x_2888_);
v_sz_boxed_2899_ = lean_unbox_usize(v_sz_2890_);
lean_dec(v_sz_2890_);
v_i_boxed_2900_ = lean_unbox_usize(v_i_2891_);
lean_dec(v_i_2891_);
v_res_2901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2886_, v_s_2887_, v___x_3585__boxed_2898_, v_as_2889_, v_sz_boxed_2899_, v_i_boxed_2900_, v_b_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec_ref(v_as_2889_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* v_t_2902_, lean_object* v_s_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v_options_2981_; uint8_t v_hasTrace_2982_; 
v_options_2981_ = lean_ctor_get(v_a_2906_, 2);
v_hasTrace_2982_ = lean_ctor_get_uint8(v_options_2981_, sizeof(void*)*1);
if (v_hasTrace_2982_ == 0)
{
v___y_2910_ = v_a_2904_;
v___y_2911_ = v_a_2905_;
v___y_2912_ = v_a_2906_;
v___y_2913_ = v_a_2907_;
goto v___jp_2909_;
}
else
{
lean_object* v_inheritedTraceOptions_2983_; lean_object* v_cls_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; 
v_inheritedTraceOptions_2983_ = lean_ctor_get(v_a_2906_, 13);
v_cls_2984_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2985_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2986_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2983_, v_options_2981_, v___x_2985_);
if (v___x_2986_ == 0)
{
v___y_2910_ = v_a_2904_;
v___y_2911_ = v_a_2905_;
v___y_2912_ = v_a_2906_;
v___y_2913_ = v_a_2907_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_inc_ref(v_t_2902_);
v___x_2987_ = l_Lean_MessageData_ofExpr(v_t_2902_);
v___x_2988_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2987_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
lean_inc_ref(v_s_2903_);
v___x_2990_ = l_Lean_MessageData_ofExpr(v_s_2903_);
v___x_2991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2989_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v___x_2992_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2984_, v___x_2991_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_dec_ref(v___x_2992_);
v___y_2910_ = v_a_2904_;
v___y_2911_ = v_a_2905_;
v___y_2912_ = v_a_2906_;
v___y_2913_ = v_a_2907_;
goto v___jp_2909_;
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec_ref(v_s_2903_);
lean_dec_ref(v_t_2902_);
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
v___jp_2909_:
{
lean_object* v___x_2914_; uint8_t v_unificationHints_2915_; 
v___x_2914_ = l_Lean_Meta_Context_config(v___y_2910_);
v_unificationHints_2915_ = lean_ctor_get_uint8(v___x_2914_, 5);
lean_dec_ref(v___x_2914_);
if (v_unificationHints_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_dec_ref(v_s_2903_);
lean_dec_ref(v_t_2902_);
v___x_2916_ = lean_box(v_unificationHints_2915_);
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
return v___x_2917_;
}
else
{
uint8_t v___x_2918_; 
v___x_2918_ = l_Lean_Expr_isMVar(v_t_2902_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; lean_object* v_env_2920_; lean_object* v___x_2921_; lean_object* v_ext_2922_; lean_object* v_toEnvExtension_2923_; lean_object* v_asyncMode_2924_; lean_object* v___x_2925_; lean_object* v_config_2926_; uint8_t v_trackZetaDelta_2927_; lean_object* v_zetaDeltaSet_2928_; lean_object* v_lctx_2929_; lean_object* v_localInstances_2930_; lean_object* v_defEqCtx_x3f_2931_; lean_object* v_synthPendingDepth_2932_; lean_object* v_canUnfold_x3f_2933_; uint8_t v_univApprox_2934_; uint8_t v_inTypeClassResolution_2935_; uint8_t v_cacheInferType_2936_; uint64_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2919_ = lean_st_ref_get(v___y_2913_);
v_env_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc_ref(v_env_2920_);
lean_dec(v___x_2919_);
v___x_2921_ = l_Lean_Meta_unificationHintExtension;
v_ext_2922_ = lean_ctor_get(v___x_2921_, 1);
v_toEnvExtension_2923_ = lean_ctor_get(v_ext_2922_, 0);
v_asyncMode_2924_ = lean_ctor_get(v_toEnvExtension_2923_, 2);
v___x_2925_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_2926_ = lean_ctor_get(v___x_2925_, 0);
v_trackZetaDelta_2927_ = lean_ctor_get_uint8(v___y_2910_, sizeof(void*)*7);
v_zetaDeltaSet_2928_ = lean_ctor_get(v___y_2910_, 1);
v_lctx_2929_ = lean_ctor_get(v___y_2910_, 2);
v_localInstances_2930_ = lean_ctor_get(v___y_2910_, 3);
v_defEqCtx_x3f_2931_ = lean_ctor_get(v___y_2910_, 4);
v_synthPendingDepth_2932_ = lean_ctor_get(v___y_2910_, 5);
v_canUnfold_x3f_2933_ = lean_ctor_get(v___y_2910_, 6);
v_univApprox_2934_ = lean_ctor_get_uint8(v___y_2910_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2935_ = lean_ctor_get_uint8(v___y_2910_, sizeof(void*)*7 + 2);
v_cacheInferType_2936_ = lean_ctor_get_uint8(v___y_2910_, sizeof(void*)*7 + 3);
v___x_2937_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2926_);
v___x_2938_ = l_Lean_Meta_instInhabitedUnificationHints_default;
v___x_2939_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2938_, v___x_2921_, v_env_2920_, v_asyncMode_2924_);
lean_inc_ref(v_config_2926_);
v___x_2940_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2940_, 0, v_config_2926_);
lean_ctor_set_uint64(v___x_2940_, sizeof(void*)*1, v___x_2937_);
lean_inc(v_canUnfold_x3f_2933_);
lean_inc(v_synthPendingDepth_2932_);
lean_inc(v_defEqCtx_x3f_2931_);
lean_inc_ref(v_localInstances_2930_);
lean_inc_ref(v_lctx_2929_);
lean_inc(v_zetaDeltaSet_2928_);
v___x_2941_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v_zetaDeltaSet_2928_);
lean_ctor_set(v___x_2941_, 2, v_lctx_2929_);
lean_ctor_set(v___x_2941_, 3, v_localInstances_2930_);
lean_ctor_set(v___x_2941_, 4, v_defEqCtx_x3f_2931_);
lean_ctor_set(v___x_2941_, 5, v_synthPendingDepth_2932_);
lean_ctor_set(v___x_2941_, 6, v_canUnfold_x3f_2933_);
lean_ctor_set_uint8(v___x_2941_, sizeof(void*)*7, v_trackZetaDelta_2927_);
lean_ctor_set_uint8(v___x_2941_, sizeof(void*)*7 + 1, v_univApprox_2934_);
lean_ctor_set_uint8(v___x_2941_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2935_);
lean_ctor_set_uint8(v___x_2941_, sizeof(void*)*7 + 3, v_cacheInferType_2936_);
lean_inc_ref(v_t_2902_);
v___x_2942_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v___x_2939_, v_t_2902_, v___x_2941_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec_ref(v___x_2941_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2944_; size_t v_sz_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_sz_2945_ = lean_array_size(v_a_2943_);
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2902_, v_s_2903_, v_unificationHints_2915_, v_a_2943_, v_sz_2945_, v___x_2946_, v___x_2944_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v_a_2943_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2961_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2961_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2961_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v_fst_2952_; 
v_fst_2952_ = lean_ctor_get(v_a_2948_, 0);
lean_inc(v_fst_2952_);
lean_dec(v_a_2948_);
if (lean_obj_tag(v_fst_2952_) == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2953_ = lean_box(v___x_2918_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2953_);
v___x_2955_ = v___x_2950_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
else
{
lean_object* v_val_2957_; lean_object* v___x_2959_; 
v_val_2957_ = lean_ctor_get(v_fst_2952_, 0);
lean_inc(v_val_2957_);
lean_dec_ref(v_fst_2952_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v_val_2957_);
v___x_2959_ = v___x_2950_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_val_2957_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
v_a_2962_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2947_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2947_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v_s_2903_);
lean_dec_ref(v_t_2902_);
v_a_2970_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2942_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2942_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
uint8_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_dec_ref(v_s_2903_);
lean_dec_ref(v_t_2902_);
v___x_2978_ = 0;
v___x_2979_ = lean_box(v___x_2978_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___boxed(lean_object* v_t_3001_, lean_object* v_s_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Lean_Meta_tryUnificationHints(v_t_3001_, v_s_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
return v_res_3008_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = lean_unsigned_to_nat(2674080740u);
v___x_3010_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3011_ = l_Lean_Name_num___override(v___x_3010_, v___x_3009_);
return v___x_3011_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3013_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3014_ = l_Lean_Name_str___override(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3016_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3017_ = l_Lean_Name_str___override(v___x_3016_, v___x_3015_);
return v___x_3017_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = lean_unsigned_to_nat(2u);
v___x_3019_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3020_ = l_Lean_Name_num___override(v___x_3019_, v___x_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3022_; uint8_t v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3022_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_3023_ = 0;
v___x_3024_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3025_ = l_Lean_registerTraceClass(v___x_3022_, v___x_3023_, v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
return v_res_3027_;
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
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
