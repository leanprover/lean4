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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_getResetPostponed___redArg(lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0;
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1;
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_value;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isDefEq"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3_value;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hint"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4_value;
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 173, 228, 229, 125, 117, 225, 10)}};
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4_value),LEAN_SCALAR_PTR_LITERAL(115, 131, 150, 64, 79, 8, 33, 190)}};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5_value;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__6 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__6_value;
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__7 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__7_value;
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = " succeeded, applying constraints"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__9 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__9_value;
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__8___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4_spec__8(lean_object* v_xs_27_, lean_object* v_v_28_, lean_object* v_i_29_){
_start:
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_array_get_size(v_xs_27_);
v___x_31_ = lean_nat_dec_lt(v_i_29_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; 
lean_dec(v_i_29_);
v___x_32_ = lean_box(0);
return v___x_32_;
}
else
{
lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_33_ = lean_array_fget_borrowed(v_xs_27_, v_i_29_);
v___x_34_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_33_, v_v_28_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_add(v_i_29_, v___x_35_);
lean_dec(v_i_29_);
v_i_29_ = v___x_36_;
goto _start;
}
else
{
lean_object* v___x_38_; 
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v_i_29_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4_spec__8___boxed(lean_object* v_xs_39_, lean_object* v_v_40_, lean_object* v_i_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4_spec__8(v_xs_39_, v_v_40_, v_i_41_);
lean_dec(v_v_40_);
lean_dec_ref(v_xs_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4(lean_object* v_xs_43_, lean_object* v_v_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4_spec__8(v_xs_43_, v_v_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4___boxed(lean_object* v_xs_47_, lean_object* v_v_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4(v_xs_47_, v_v_48_);
lean_dec(v_v_48_);
lean_dec_ref(v_xs_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10_spec__11___redArg(lean_object* v_x_50_, lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_ks_54_; lean_object* v_vs_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_79_; 
v_ks_54_ = lean_ctor_get(v_x_50_, 0);
v_vs_55_ = lean_ctor_get(v_x_50_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_79_ == 0)
{
v___x_57_ = v_x_50_;
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_vs_55_);
lean_inc(v_ks_54_);
lean_dec(v_x_50_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_array_get_size(v_ks_54_);
v___x_60_ = lean_nat_dec_lt(v_x_51_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
lean_dec(v_x_51_);
v___x_61_ = lean_array_push(v_ks_54_, v_x_52_);
v___x_62_ = lean_array_push(v_vs_55_, v_x_53_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_62_);
lean_ctor_set(v___x_57_, 0, v___x_61_);
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
else
{
lean_object* v_k_x27_66_; uint8_t v___x_67_; 
v_k_x27_66_ = lean_array_fget_borrowed(v_ks_54_, v_x_51_);
v___x_67_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_52_, v_k_x27_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_69_; 
if (v_isShared_58_ == 0)
{
v___x_69_ = v___x_57_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_ks_54_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_vs_55_);
v___x_69_ = v_reuseFailAlloc_73_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_x_51_, v___x_70_);
lean_dec(v_x_51_);
v_x_50_ = v___x_69_;
v_x_51_ = v___x_71_;
goto _start;
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = lean_array_fset(v_ks_54_, v_x_51_, v_x_52_);
v___x_75_ = lean_array_fset(v_vs_55_, v_x_51_, v_x_53_);
lean_dec(v_x_51_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_75_);
lean_ctor_set(v___x_57_, 0, v___x_74_);
v___x_77_ = v___x_57_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10___redArg(lean_object* v_n_80_, lean_object* v_k_81_, lean_object* v_v_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10_spec__11___redArg(v_n_80_, v___x_83_, v_k_81_, v_v_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(lean_object* v_x_86_, size_t v_x_87_, size_t v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v_es_91_; size_t v___x_92_; size_t v___x_93_; lean_object* v_j_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_es_91_ = lean_ctor_get(v_x_86_, 0);
v___x_92_ = ((size_t)31ULL);
v___x_93_ = lean_usize_land(v_x_87_, v___x_92_);
v_j_94_ = lean_usize_to_nat(v___x_93_);
v___x_95_ = lean_array_get_size(v_es_91_);
v___x_96_ = lean_nat_dec_lt(v_j_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_dec(v_j_94_);
lean_dec(v_x_90_);
lean_dec(v_x_89_);
return v_x_86_;
}
else
{
lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_135_; 
lean_inc_ref(v_es_91_);
v_isSharedCheck_135_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v_x_86_, 0);
lean_dec(v_unused_136_);
v___x_98_ = v_x_86_;
v_isShared_99_ = v_isSharedCheck_135_;
goto v_resetjp_97_;
}
else
{
lean_dec(v_x_86_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_135_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_v_100_; lean_object* v___x_101_; lean_object* v_xs_x27_102_; lean_object* v___y_104_; 
v_v_100_ = lean_array_fget(v_es_91_, v_j_94_);
v___x_101_ = lean_box(0);
v_xs_x27_102_ = lean_array_fset(v_es_91_, v_j_94_, v___x_101_);
switch(lean_obj_tag(v_v_100_))
{
case 0:
{
lean_object* v_key_109_; lean_object* v_val_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_120_; 
v_key_109_ = lean_ctor_get(v_v_100_, 0);
v_val_110_ = lean_ctor_get(v_v_100_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_v_100_);
if (v_isSharedCheck_120_ == 0)
{
v___x_112_ = v_v_100_;
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_val_110_);
lean_inc(v_key_109_);
lean_dec(v_v_100_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
uint8_t v___x_114_; 
v___x_114_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_89_, v_key_109_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_del_object(v___x_112_);
v___x_115_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_109_, v_val_110_, v_x_89_, v_x_90_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
v___y_104_ = v___x_116_;
goto v___jp_103_;
}
else
{
lean_object* v___x_118_; 
lean_dec(v_val_110_);
lean_dec(v_key_109_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 1, v_x_90_);
lean_ctor_set(v___x_112_, 0, v_x_89_);
v___x_118_ = v___x_112_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_x_89_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_x_90_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
v___y_104_ = v___x_118_;
goto v___jp_103_;
}
}
}
}
case 1:
{
lean_object* v_node_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_133_; 
v_node_121_ = lean_ctor_get(v_v_100_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_v_100_);
if (v_isSharedCheck_133_ == 0)
{
v___x_123_ = v_v_100_;
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_node_121_);
lean_dec(v_v_100_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_125_ = ((size_t)5ULL);
v___x_126_ = lean_usize_shift_right(v_x_87_, v___x_125_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_add(v_x_88_, v___x_127_);
v___x_129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(v_node_121_, v___x_126_, v___x_128_, v_x_89_, v_x_90_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_129_);
v___x_131_ = v___x_123_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
v___y_104_ = v___x_131_;
goto v___jp_103_;
}
}
}
default: 
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_x_89_);
lean_ctor_set(v___x_134_, 1, v_x_90_);
v___y_104_ = v___x_134_;
goto v___jp_103_;
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = lean_array_fset(v_xs_x27_102_, v_j_94_, v___y_104_);
lean_dec(v_j_94_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_105_);
v___x_107_ = v___x_98_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
else
{
lean_object* v_ks_137_; lean_object* v_vs_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_158_; 
v_ks_137_ = lean_ctor_get(v_x_86_, 0);
v_vs_138_ = lean_ctor_get(v_x_86_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_158_ == 0)
{
v___x_140_ = v_x_86_;
v_isShared_141_ = v_isSharedCheck_158_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_vs_138_);
lean_inc(v_ks_137_);
lean_dec(v_x_86_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_158_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_ks_137_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_vs_138_);
v___x_143_ = v_reuseFailAlloc_157_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v_newNode_144_; uint8_t v___y_146_; size_t v___x_152_; uint8_t v___x_153_; 
v_newNode_144_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10___redArg(v___x_143_, v_x_89_, v_x_90_);
v___x_152_ = ((size_t)7ULL);
v___x_153_ = lean_usize_dec_le(v___x_152_, v_x_88_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_144_);
v___x_155_ = lean_unsigned_to_nat(4u);
v___x_156_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
lean_dec(v___x_154_);
v___y_146_ = v___x_156_;
goto v___jp_145_;
}
else
{
v___y_146_ = v___x_153_;
goto v___jp_145_;
}
v___jp_145_:
{
if (v___y_146_ == 0)
{
lean_object* v_ks_147_; lean_object* v_vs_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_ks_147_ = lean_ctor_get(v_newNode_144_, 0);
lean_inc_ref(v_ks_147_);
v_vs_148_ = lean_ctor_get(v_newNode_144_, 1);
lean_inc_ref(v_vs_148_);
lean_dec_ref(v_newNode_144_);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___closed__0);
v___x_151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg(v_x_88_, v_ks_147_, v_vs_148_, v___x_149_, v___x_150_);
lean_dec_ref(v_vs_148_);
lean_dec_ref(v_ks_147_);
return v___x_151_;
}
else
{
return v_newNode_144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg(size_t v_depth_159_, lean_object* v_keys_160_, lean_object* v_vals_161_, lean_object* v_i_162_, lean_object* v_entries_163_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_array_get_size(v_keys_160_);
v___x_165_ = lean_nat_dec_lt(v_i_162_, v___x_164_);
if (v___x_165_ == 0)
{
lean_dec(v_i_162_);
return v_entries_163_;
}
else
{
lean_object* v_k_166_; lean_object* v_v_167_; uint64_t v___x_168_; size_t v_h_169_; size_t v___x_170_; lean_object* v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v_h_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_k_166_ = lean_array_fget_borrowed(v_keys_160_, v_i_162_);
v_v_167_ = lean_array_fget_borrowed(v_vals_161_, v_i_162_);
v___x_168_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_166_);
v_h_169_ = lean_uint64_to_usize(v___x_168_);
v___x_170_ = ((size_t)5ULL);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_sub(v_depth_159_, v___x_172_);
v___x_174_ = lean_usize_mul(v___x_170_, v___x_173_);
v_h_175_ = lean_usize_shift_right(v_h_169_, v___x_174_);
v___x_176_ = lean_nat_add(v_i_162_, v___x_171_);
lean_dec(v_i_162_);
lean_inc(v_v_167_);
lean_inc(v_k_166_);
v___x_177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(v_entries_163_, v_h_175_, v_depth_159_, v_k_166_, v_v_167_);
v_i_162_ = v___x_176_;
v_entries_163_ = v___x_177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_depth_179_, lean_object* v_keys_180_, lean_object* v_vals_181_, lean_object* v_i_182_, lean_object* v_entries_183_){
_start:
{
size_t v_depth_boxed_184_; lean_object* v_res_185_; 
v_depth_boxed_184_ = lean_unbox_usize(v_depth_179_);
lean_dec(v_depth_179_);
v_res_185_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg(v_depth_boxed_184_, v_keys_180_, v_vals_181_, v_i_182_, v_entries_183_);
lean_dec_ref(v_vals_181_);
lean_dec_ref(v_keys_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
size_t v_x_1660__boxed_191_; size_t v_x_1661__boxed_192_; lean_object* v_res_193_; 
v_x_1660__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_x_1661__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_res_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(v_x_186_, v_x_1660__boxed_191_, v_x_1661__boxed_192_, v_x_189_, v_x_190_);
return v_res_193_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
lean_object* v_fst_196_; lean_object* v_fst_197_; uint8_t v___x_198_; 
v_fst_196_ = lean_ctor_get(v_a_194_, 0);
v_fst_197_ = lean_ctor_get(v_b_195_, 0);
v___x_198_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_196_, v_fst_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_a_199_, v_b_200_);
lean_dec_ref(v_b_200_);
lean_dec_ref(v_a_199_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(lean_object* v_x_203_, lean_object* v_keys_204_, lean_object* v_v_205_, lean_object* v_k_206_, lean_object* v_x_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_c_210_; lean_object* v___x_211_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_x_203_, v___x_208_);
v_c_210_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_204_, v_v_205_, v___x_209_);
lean_dec(v___x_209_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v_k_206_);
lean_ctor_set(v___x_211_, 1, v_c_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_x_212_, lean_object* v_keys_213_, lean_object* v_v_214_, lean_object* v_k_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(v_x_212_, v_keys_213_, v_v_214_, v_k_215_, v_x_216_);
lean_dec_ref(v_keys_213_);
lean_dec(v_x_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_vs_218_, lean_object* v_v_219_, lean_object* v_i_220_){
_start:
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_array_get_size(v_vs_218_);
v___x_222_ = lean_nat_dec_lt(v_i_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec(v_i_220_);
v___x_223_ = lean_array_push(v_vs_218_, v_v_219_);
return v___x_223_;
}
else
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = lean_array_fget_borrowed(v_vs_218_, v_i_220_);
v___x_225_ = lean_name_eq(v_v_219_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_add(v_i_220_, v___x_226_);
lean_dec(v_i_220_);
v_i_220_ = v___x_227_;
goto _start;
}
else
{
lean_object* v___x_229_; 
v___x_229_ = lean_array_fset(v_vs_218_, v_i_220_, v_v_219_);
lean_dec(v_i_220_);
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(lean_object* v_vs_230_, lean_object* v_v_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(v_vs_230_, v_v_231_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_238_, lean_object* v_keys_239_, lean_object* v_v_240_, lean_object* v_k_241_, lean_object* v_as_242_, lean_object* v_k_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_mid_248_; lean_object* v_midVal_249_; uint8_t v___x_250_; 
v___x_246_ = lean_nat_add(v_x_244_, v_x_245_);
v___x_247_ = lean_unsigned_to_nat(1u);
v_mid_248_ = lean_nat_shiftr(v___x_246_, v___x_247_);
lean_dec(v___x_246_);
v_midVal_249_ = lean_array_fget(v_as_242_, v_mid_248_);
v___x_250_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_midVal_249_, v_k_243_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
lean_dec(v_x_245_);
v___x_251_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_k_243_, v_midVal_249_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; uint8_t v___x_253_; 
lean_dec(v_x_244_);
v___x_252_ = lean_array_get_size(v_as_242_);
v___x_253_ = lean_nat_dec_lt(v_mid_248_, v___x_252_);
if (v___x_253_ == 0)
{
lean_dec(v_midVal_249_);
lean_dec(v_mid_248_);
lean_dec(v_k_241_);
lean_dec(v_v_240_);
return v_as_242_;
}
else
{
lean_object* v_snd_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_266_; 
v_snd_254_ = lean_ctor_get(v_midVal_249_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_midVal_249_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v_midVal_249_, 0);
lean_dec(v_unused_267_);
v___x_256_ = v_midVal_249_;
v_isShared_257_ = v_isSharedCheck_266_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_snd_254_);
lean_dec(v_midVal_249_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_266_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v_xs_x27_259_; lean_object* v___x_260_; lean_object* v_c_261_; lean_object* v___x_263_; 
v___x_258_ = lean_box(0);
v_xs_x27_259_ = lean_array_fset(v_as_242_, v_mid_248_, v___x_258_);
v___x_260_ = lean_nat_add(v_x_238_, v___x_247_);
v_c_261_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_239_, v_v_240_, v___x_260_, v_snd_254_);
lean_dec(v___x_260_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v_c_261_);
lean_ctor_set(v___x_256_, 0, v_k_241_);
v___x_263_ = v___x_256_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_k_241_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_c_261_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_array_fset(v_xs_x27_259_, v_mid_248_, v___x_263_);
lean_dec(v_mid_248_);
return v___x_264_;
}
}
}
}
else
{
lean_dec(v_midVal_249_);
v_x_245_ = v_mid_248_;
goto _start;
}
}
else
{
uint8_t v___x_269_; 
lean_dec(v_midVal_249_);
v___x_269_ = lean_nat_dec_eq(v_mid_248_, v_x_244_);
if (v___x_269_ == 0)
{
lean_dec(v_x_244_);
v_x_244_ = v_mid_248_;
goto _start;
}
else
{
lean_object* v___x_271_; lean_object* v_c_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_j_275_; lean_object* v_as_276_; lean_object* v___x_277_; 
lean_dec(v_mid_248_);
lean_dec(v_x_245_);
v___x_271_ = lean_nat_add(v_x_238_, v___x_247_);
v_c_272_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_239_, v_v_240_, v___x_271_);
lean_dec(v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_k_241_);
lean_ctor_set(v___x_273_, 1, v_c_272_);
v___x_274_ = lean_nat_add(v_x_244_, v___x_247_);
lean_dec(v_x_244_);
v_j_275_ = lean_array_get_size(v_as_242_);
v_as_276_ = lean_array_push(v_as_242_, v___x_273_);
v___x_277_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_274_, v_as_276_, v_j_275_);
lean_dec(v___x_274_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(lean_object* v_x_278_, lean_object* v_keys_279_, lean_object* v_v_280_, lean_object* v_k_281_, lean_object* v_as_282_, lean_object* v_k_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_array_get_size(v_as_282_);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_nat_dec_eq(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_array_fget_borrowed(v_as_282_, v___x_285_);
v___x_288_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_k_283_, v___x_287_);
if (v___x_288_ == 0)
{
uint8_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v___x_287_, v_k_283_);
v___x_290_ = lean_bool_not(v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_sub(v___x_284_, v___x_291_);
v___x_293_ = lean_array_fget_borrowed(v_as_282_, v___x_292_);
v___x_294_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v___x_293_, v_k_283_);
if (v___x_294_ == 0)
{
uint8_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_k_283_, v___x_293_);
v___x_296_ = lean_bool_not(v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg(v_x_278_, v_keys_279_, v_v_280_, v_k_281_, v_as_282_, v_k_283_, v___x_285_, v___x_292_);
return v___x_297_;
}
else
{
uint8_t v___x_298_; 
v___x_298_ = lean_nat_dec_lt(v___x_292_, v___x_284_);
if (v___x_298_ == 0)
{
lean_dec(v___x_292_);
lean_dec(v_k_281_);
lean_dec(v_v_280_);
return v_as_282_;
}
else
{
lean_object* v___x_299_; lean_object* v_xs_x27_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_inc(v___x_293_);
v___x_299_ = lean_box(0);
v_xs_x27_300_ = lean_array_fset(v_as_282_, v___x_292_, v___x_299_);
v___x_301_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(v_x_278_, v_keys_279_, v_v_280_, v_k_281_, v___x_293_);
v___x_302_ = lean_array_fset(v_xs_x27_300_, v___x_292_, v___x_301_);
lean_dec(v___x_292_);
return v___x_302_;
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v___x_292_);
v___x_303_ = lean_box(0);
v___x_304_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(v_x_278_, v_keys_279_, v_v_280_, v_k_281_, v___x_303_);
v___x_305_ = lean_array_push(v_as_282_, v___x_304_);
return v___x_305_;
}
}
else
{
uint8_t v___x_306_; 
v___x_306_ = lean_nat_dec_lt(v___x_285_, v___x_284_);
if (v___x_306_ == 0)
{
lean_dec(v_k_281_);
lean_dec(v_v_280_);
return v_as_282_;
}
else
{
lean_object* v___x_307_; lean_object* v_xs_x27_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_inc(v___x_287_);
v___x_307_ = lean_box(0);
v_xs_x27_308_ = lean_array_fset(v_as_282_, v___x_285_, v___x_307_);
v___x_309_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(v_x_278_, v_keys_279_, v_v_280_, v_k_281_, v___x_287_);
v___x_310_ = lean_array_fset(v_xs_x27_308_, v___x_285_, v___x_309_);
return v___x_310_;
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_as_313_; lean_object* v___x_314_; 
v___x_311_ = lean_box(0);
v___x_312_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(v_x_278_, v_keys_279_, v_v_280_, v_k_281_, v___x_311_);
v_as_313_ = lean_array_push(v_as_282_, v___x_312_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_285_, v_as_313_, v___x_284_);
return v___x_314_;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_box(0);
v___x_316_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(v_x_278_, v_keys_279_, v_v_280_, v_k_281_, v___x_315_);
v___x_317_ = lean_array_push(v_as_282_, v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object* v_keys_318_, lean_object* v_v_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_vs_322_; lean_object* v_children_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_340_; 
v_vs_322_ = lean_ctor_get(v_x_321_, 0);
v_children_323_ = lean_ctor_get(v_x_321_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_340_ == 0)
{
v___x_325_ = v_x_321_;
v_isShared_326_ = v_isSharedCheck_340_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_children_323_);
lean_inc(v_vs_322_);
lean_dec(v_x_321_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_340_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_array_get_size(v_keys_318_);
v___x_328_ = lean_nat_dec_lt(v_x_320_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_329_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(v_vs_322_, v_v_319_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_329_);
v___x_331_ = v___x_325_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_children_323_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
else
{
lean_object* v_k_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v_c_336_; lean_object* v___x_338_; 
v_k_333_ = lean_array_fget_borrowed(v_keys_318_, v_x_320_);
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__1));
lean_inc_n(v_k_333_, 2);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v_k_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v_c_336_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(v_x_320_, v_keys_318_, v_v_319_, v_k_333_, v_children_323_, v___x_335_);
lean_dec_ref_known(v___x_335_, 2);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v_c_336_);
v___x_338_ = v___x_325_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_vs_322_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_c_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(lean_object* v_x_341_, lean_object* v_keys_342_, lean_object* v_v_343_, lean_object* v_k_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_snd_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_356_; 
v_snd_346_ = lean_ctor_get(v_x_345_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; 
v_unused_357_ = lean_ctor_get(v_x_345_, 0);
lean_dec(v_unused_357_);
v___x_348_ = v_x_345_;
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snd_346_);
lean_dec(v_x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_c_352_; lean_object* v___x_354_; 
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_x_341_, v___x_350_);
v_c_352_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_342_, v_v_343_, v___x_351_, v_snd_346_);
lean_dec(v___x_351_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v_c_352_);
lean_ctor_set(v___x_348_, 0, v_k_344_);
v___x_354_ = v___x_348_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_k_344_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_c_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_358_, lean_object* v_keys_359_, lean_object* v_v_360_, lean_object* v_k_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(v_x_358_, v_keys_359_, v_v_360_, v_k_361_, v_x_362_);
lean_dec_ref(v_keys_359_);
lean_dec(v_x_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object* v_keys_364_, lean_object* v_v_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_364_, v_v_365_, v_x_366_, v_x_367_);
lean_dec(v_x_366_);
lean_dec_ref(v_keys_364_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_369_, lean_object* v_keys_370_, lean_object* v_v_371_, lean_object* v_k_372_, lean_object* v_as_373_, lean_object* v_k_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg(v_x_369_, v_keys_370_, v_v_371_, v_k_372_, v_as_373_, v_k_374_, v_x_375_, v_x_376_);
lean_dec_ref(v_k_374_);
lean_dec_ref(v_keys_370_);
lean_dec(v_x_369_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___boxed(lean_object* v_x_378_, lean_object* v_keys_379_, lean_object* v_v_380_, lean_object* v_k_381_, lean_object* v_as_382_, lean_object* v_k_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(v_x_378_, v_keys_379_, v_v_380_, v_k_381_, v_as_382_, v_k_383_);
lean_dec_ref(v_k_383_);
lean_dec_ref(v_keys_379_);
lean_dec(v_x_378_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(lean_object* v_keys_385_, lean_object* v_v_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_385_, v_v_386_, v___x_388_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v_val_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_400_; 
v_val_391_ = lean_ctor_get(v_x_387_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_x_387_);
if (v_isSharedCheck_400_ == 0)
{
v___x_393_ = v_x_387_;
v_isShared_394_ = v_isSharedCheck_400_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_val_391_);
lean_dec(v_x_387_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_400_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_385_, v_v_386_, v___x_395_, v_val_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_396_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_401_, lean_object* v_v_402_, lean_object* v_x_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_401_, v_v_402_, v_x_403_);
lean_dec_ref(v_keys_401_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(lean_object* v_keys_405_, lean_object* v_v_406_, lean_object* v_x_407_, size_t v_x_408_, size_t v_x_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
lean_object* v_es_411_; size_t v___x_412_; size_t v___x_413_; lean_object* v_j_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_es_411_ = lean_ctor_get(v_x_407_, 0);
v___x_412_ = ((size_t)31ULL);
v___x_413_ = lean_usize_land(v_x_408_, v___x_412_);
v_j_414_ = lean_usize_to_nat(v___x_413_);
v___x_415_ = lean_array_get_size(v_es_411_);
v___x_416_ = lean_nat_dec_lt(v_j_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_dec(v_j_414_);
lean_dec(v_x_410_);
lean_dec(v_v_406_);
return v_x_407_;
}
else
{
lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_484_; 
lean_inc_ref(v_es_411_);
v_isSharedCheck_484_ = !lean_is_exclusive(v_x_407_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v_x_407_, 0);
lean_dec(v_unused_485_);
v___x_418_ = v_x_407_;
v_isShared_419_ = v_isSharedCheck_484_;
goto v_resetjp_417_;
}
else
{
lean_dec(v_x_407_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_484_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_v_420_; lean_object* v___x_421_; lean_object* v_xs_x27_422_; lean_object* v___y_424_; 
v_v_420_ = lean_array_fget(v_es_411_, v_j_414_);
v___x_421_ = lean_box(0);
v_xs_x27_422_ = lean_array_fset(v_es_411_, v_j_414_, v___x_421_);
switch(lean_obj_tag(v_v_420_))
{
case 0:
{
lean_object* v_key_429_; lean_object* v_val_430_; uint8_t v___x_431_; 
v_key_429_ = lean_ctor_get(v_v_420_, 0);
v_val_430_ = lean_ctor_get(v_v_420_, 1);
v___x_431_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_410_, v_key_429_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_box(0);
v___x_433_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_405_, v_v_406_, v___x_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_dec(v_x_410_);
v___y_424_ = v_v_420_;
goto v___jp_423_;
}
else
{
lean_object* v_val_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_442_; 
lean_inc(v_val_430_);
lean_inc(v_key_429_);
lean_dec_ref_known(v_v_420_, 2);
v_val_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_442_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_val_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_429_, v_val_430_, v_x_410_, v_val_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
v___y_424_ = v___x_440_;
goto v___jp_423_;
}
}
}
}
else
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_453_; 
lean_inc(v_val_430_);
v_isSharedCheck_453_ = !lean_is_exclusive(v_v_420_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; 
v_unused_454_ = lean_ctor_get(v_v_420_, 1);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_v_420_, 0);
lean_dec(v_unused_455_);
v___x_444_ = v_v_420_;
v_isShared_445_ = v_isSharedCheck_453_;
goto v_resetjp_443_;
}
else
{
lean_dec(v_v_420_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_453_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_val_430_);
v___x_447_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_405_, v_v_406_, v___x_446_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; 
lean_del_object(v___x_444_);
lean_dec(v_x_410_);
v___x_448_ = lean_box(2);
v___y_424_ = v___x_448_;
goto v___jp_423_;
}
else
{
lean_object* v_val_449_; lean_object* v___x_451_; 
v_val_449_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v___x_447_, 1);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v_val_449_);
lean_ctor_set(v___x_444_, 0, v_x_410_);
v___x_451_ = v___x_444_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_x_410_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_val_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
v___y_424_ = v___x_451_;
goto v___jp_423_;
}
}
}
}
}
case 1:
{
lean_object* v_node_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_479_; 
v_node_456_ = lean_ctor_get(v_v_420_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_v_420_);
if (v_isSharedCheck_479_ == 0)
{
v___x_458_ = v_v_420_;
v_isShared_459_ = v_isSharedCheck_479_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_node_456_);
lean_dec(v_v_420_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_479_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
size_t v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; lean_object* v_newNode_464_; lean_object* v___x_465_; 
v___x_460_ = ((size_t)5ULL);
v___x_461_ = lean_usize_shift_right(v_x_408_, v___x_460_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_add(v_x_409_, v___x_462_);
v_newNode_464_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(v_keys_405_, v_v_406_, v_node_456_, v___x_461_, v___x_463_, v_x_410_);
lean_inc_ref(v_newNode_464_);
v___x_465_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_467_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v_newNode_464_);
v___x_467_ = v___x_458_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_newNode_464_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
v___y_424_ = v___x_467_;
goto v___jp_423_;
}
}
else
{
lean_object* v_val_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_newNode_464_);
lean_del_object(v___x_458_);
v_val_469_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_465_, 1);
v_fst_470_ = lean_ctor_get(v_val_469_, 0);
v_snd_471_ = lean_ctor_get(v_val_469_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_val_469_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v_val_469_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_inc(v_fst_470_);
lean_dec(v_val_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_fst_470_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_snd_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
v___y_424_ = v___x_476_;
goto v___jp_423_;
}
}
}
}
}
default: 
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_box(0);
v___x_481_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_405_, v_v_406_, v___x_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_dec(v_x_410_);
v___y_424_ = v_v_420_;
goto v___jp_423_;
}
else
{
lean_object* v_val_482_; lean_object* v___x_483_; 
v_val_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v___x_481_, 1);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v_x_410_);
lean_ctor_set(v___x_483_, 1, v_val_482_);
v___y_424_ = v___x_483_;
goto v___jp_423_;
}
}
}
v___jp_423_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_array_fset(v_xs_x27_422_, v_j_414_, v___y_424_);
lean_dec(v_j_414_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_425_);
v___x_427_ = v___x_418_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
else
{
lean_object* v_ks_486_; lean_object* v_vs_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_520_; 
v_ks_486_ = lean_ctor_get(v_x_407_, 0);
v_vs_487_ = lean_ctor_get(v_x_407_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_407_);
if (v_isSharedCheck_520_ == 0)
{
v___x_489_ = v_x_407_;
v_isShared_490_ = v_isSharedCheck_520_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_vs_487_);
lean_inc(v_ks_486_);
lean_dec(v_x_407_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_520_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; 
v___x_491_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4(v_ks_486_, v_x_410_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_493_; 
if (v_isShared_490_ == 0)
{
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_ks_486_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_vs_487_);
v___x_493_ = v_reuseFailAlloc_498_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_box(0);
v___x_495_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_405_, v_v_406_, v___x_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_dec(v_x_410_);
return v___x_493_;
}
else
{
lean_object* v_val_496_; lean_object* v___x_497_; 
v_val_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(v___x_493_, v_x_408_, v_x_409_, v_x_410_, v_val_496_);
return v___x_497_;
}
}
}
else
{
lean_object* v_val_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_519_; 
v_val_499_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_519_ == 0)
{
v___x_501_ = v___x_491_;
v_isShared_502_ = v_isSharedCheck_519_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_val_499_);
lean_dec(v___x_491_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_519_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_v_x27_503_; lean_object* v_keys_504_; lean_object* v_vals_505_; lean_object* v___x_507_; 
v_v_x27_503_ = lean_array_fget(v_vs_487_, v_val_499_);
lean_inc(v_val_499_);
v_keys_504_ = l_Array_eraseIdx___redArg(v_ks_486_, v_val_499_);
v_vals_505_ = l_Array_eraseIdx___redArg(v_vs_487_, v_val_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v_v_x27_503_);
v___x_507_ = v___x_501_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_v_x27_503_);
v___x_507_ = v_reuseFailAlloc_518_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_405_, v_v_406_, v___x_507_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v___x_510_; 
lean_dec(v_x_410_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_vals_505_);
lean_ctor_set(v___x_489_, 0, v_keys_504_);
v___x_510_ = v___x_489_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_keys_504_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_vals_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v_val_512_; lean_object* v_keys_513_; lean_object* v_vals_514_; lean_object* v___x_516_; 
v_val_512_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v___x_508_, 1);
v_keys_513_ = lean_array_push(v_keys_504_, v_x_410_);
v_vals_514_ = lean_array_push(v_vals_505_, v_val_512_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_vals_514_);
lean_ctor_set(v___x_489_, 0, v_keys_513_);
v___x_516_ = v___x_489_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_keys_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_vals_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___boxed(lean_object* v_keys_521_, lean_object* v_v_522_, lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
size_t v_x_2089__boxed_527_; size_t v_x_2090__boxed_528_; lean_object* v_res_529_; 
v_x_2089__boxed_527_ = lean_unbox_usize(v_x_524_);
lean_dec(v_x_524_);
v_x_2090__boxed_528_ = lean_unbox_usize(v_x_525_);
lean_dec(v_x_525_);
v_res_529_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(v_keys_521_, v_v_522_, v_x_523_, v_x_2089__boxed_527_, v_x_2090__boxed_528_, v_x_526_);
lean_dec_ref(v_keys_521_);
return v_res_529_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(lean_object* v_msg_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0);
v___x_533_ = lean_panic_fn_borrowed(v___x_532_, v_msg_531_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_537_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2));
v___x_538_ = lean_unsigned_to_nat(23u);
v___x_539_ = lean_unsigned_to_nat(166u);
v___x_540_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1));
v___x_541_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0));
v___x_542_ = l_mkPanicMessageWithDecl(v___x_541_, v___x_540_, v___x_539_, v___x_538_, v___x_537_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(lean_object* v_d_543_, lean_object* v_keys_544_, lean_object* v_v_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_546_ = lean_array_get_size(v_keys_544_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_nat_dec_eq(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v_k_550_; uint64_t v___x_551_; size_t v_h_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_549_ = lean_box(0);
v_k_550_ = lean_array_get_borrowed(v___x_549_, v_keys_544_, v___x_547_);
v___x_551_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_550_);
v_h_552_ = lean_uint64_to_usize(v___x_551_);
v___x_553_ = ((size_t)1ULL);
lean_inc(v_k_550_);
v___x_554_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(v_keys_544_, v_v_545_, v_d_543_, v_h_552_, v___x_553_, v_k_550_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_v_545_);
lean_dec_ref(v_d_543_);
v___x_555_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3);
v___x_556_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v___x_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___boxed(lean_object* v_d_557_, lean_object* v_keys_558_, lean_object* v_v_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_d_557_, v_keys_558_, v_v_559_);
lean_dec_ref(v_keys_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* v_hints_561_, lean_object* v_e_562_){
_start:
{
lean_object* v_keys_563_; lean_object* v_val_564_; lean_object* v___x_565_; 
v_keys_563_ = lean_ctor_get(v_e_562_, 0);
lean_inc_ref(v_keys_563_);
v_val_564_ = lean_ctor_get(v_e_562_, 1);
lean_inc(v_val_564_);
lean_dec_ref(v_e_562_);
v___x_565_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_hints_561_, v_keys_563_, v_val_564_);
lean_dec_ref(v_keys_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_566_, lean_object* v_x_567_, size_t v_x_568_, size_t v_x_569_, lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(v_x_567_, v_x_568_, v_x_569_, v_x_570_, v_x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
size_t v_x_2357__boxed_579_; size_t v_x_2358__boxed_580_; lean_object* v_res_581_; 
v_x_2357__boxed_579_ = lean_unbox_usize(v_x_575_);
lean_dec(v_x_575_);
v_x_2358__boxed_580_ = lean_unbox_usize(v_x_576_);
lean_dec(v_x_576_);
v_res_581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5(v_00_u03b2_573_, v_x_574_, v_x_2357__boxed_579_, v_x_2358__boxed_580_, v_x_577_, v_x_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_582_, lean_object* v_keys_583_, lean_object* v_v_584_, lean_object* v_k_585_, lean_object* v_as_586_, lean_object* v_k_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg(v_x_582_, v_keys_583_, v_v_584_, v_k_585_, v_as_586_, v_k_587_, v_x_588_, v_x_589_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_593_, lean_object* v_keys_594_, lean_object* v_v_595_, lean_object* v_k_596_, lean_object* v_as_597_, lean_object* v_k_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5(v_x_593_, v_keys_594_, v_v_595_, v_k_596_, v_as_597_, v_k_598_, v_x_599_, v_x_600_, v_x_601_, v_x_602_);
lean_dec_ref(v_k_598_);
lean_dec_ref(v_keys_594_);
lean_dec(v_x_593_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_604_, lean_object* v_n_605_, lean_object* v_k_606_, lean_object* v_v_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10___redArg(v_n_605_, v_k_606_, v_v_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_609_, size_t v_depth_610_, lean_object* v_keys_611_, lean_object* v_vals_612_, lean_object* v_heq_613_, lean_object* v_i_614_, lean_object* v_entries_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg(v_depth_610_, v_keys_611_, v_vals_612_, v_i_614_, v_entries_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_617_, lean_object* v_depth_618_, lean_object* v_keys_619_, lean_object* v_vals_620_, lean_object* v_heq_621_, lean_object* v_i_622_, lean_object* v_entries_623_){
_start:
{
size_t v_depth_boxed_624_; lean_object* v_res_625_; 
v_depth_boxed_624_ = lean_unbox_usize(v_depth_618_);
lean_dec(v_depth_618_);
v_res_625_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11(v_00_u03b2_617_, v_depth_boxed_624_, v_keys_619_, v_vals_620_, v_heq_621_, v_i_622_, v_entries_623_);
lean_dec_ref(v_vals_620_);
lean_dec_ref(v_keys_619_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10_spec__11(lean_object* v_00_u03b2_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10_spec__11___redArg(v_x_627_, v_x_628_, v_x_629_, v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object* v_x_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v_a_633_);
lean_inc_ref_n(v___x_634_, 2);
v___x_635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
lean_ctor_set(v___x_635_, 2, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_x_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v_x_636_, v_a_637_);
lean_dec_ref(v_x_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object* v___y_639_){
_start:
{
lean_inc_ref(v___y_639_);
return v___y_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v___y_640_);
lean_dec_ref(v___y_640_);
return v_res_641_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_652_; lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___f_652_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___f_653_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_654_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_656_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
lean_ctor_set(v___x_657_, 2, v___x_654_);
lean_ctor_set(v___x_657_, 3, v___f_653_);
lean_ctor_set(v___x_657_, 4, v___f_652_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_);
v___x_660_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
return v_res_662_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2));
v___x_668_ = l_Lean_stringToMessageData(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object* v_e_669_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1));
v___x_671_ = lean_unsigned_to_nat(3u);
v___x_672_ = l_Lean_Expr_isAppOfArity(v_e_669_, v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_673_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3);
v___x_674_ = l_Lean_indentExpr(v_e_669_);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_677_ = l_Lean_Expr_appFn_x21(v_e_669_);
v___x_678_ = l_Lean_Expr_appArg_x21(v___x_677_);
lean_dec_ref(v___x_677_);
v___x_679_ = l_Lean_Expr_appArg_x21(v_e_669_);
lean_dec_ref(v_e_669_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object* v_e_685_, lean_object* v_cs_686_){
_start:
{
if (lean_obj_tag(v_e_685_) == 7)
{
lean_object* v_binderType_687_; lean_object* v_body_688_; lean_object* v___x_689_; 
v_binderType_687_ = lean_ctor_get(v_e_685_, 1);
v_body_688_ = lean_ctor_get(v_e_685_, 2);
lean_inc_ref(v_binderType_687_);
v___x_689_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_binderType_687_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref_known(v_e_685_, 3);
lean_dec_ref(v_cs_686_);
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_711_; 
v_a_698_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_711_ == 0)
{
v___x_700_ = v___x_689_;
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_689_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_Expr_hasLooseBVars(v_body_688_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_inc_ref(v_body_688_);
lean_del_object(v___x_700_);
lean_dec_ref_known(v_e_685_, 3);
v___x_703_ = lean_array_push(v_cs_686_, v_a_698_);
v_e_685_ = v_body_688_;
v_cs_686_ = v___x_703_;
goto _start;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
lean_dec(v_a_698_);
lean_dec_ref(v_cs_686_);
v___x_705_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1);
v___x_706_ = l_Lean_indentExpr(v_e_685_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
lean_ctor_set(v___x_700_, 0, v___x_707_);
v___x_709_ = v___x_700_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
else
{
lean_object* v___x_712_; 
v___x_712_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_e_685_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v_cs_686_);
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_730_; 
v_a_721_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_730_ == 0)
{
v___x_723_ = v___x_712_;
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_712_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = lean_array_to_list(v_cs_686_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_a_721_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_726_);
v___x_728_ = v___x_723_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object* v_e_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0));
v___x_735_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(v_e_733_, v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(lean_object* v_msgData_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_env_743_; lean_object* v___x_744_; lean_object* v_mctx_745_; lean_object* v_lctx_746_; lean_object* v_options_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_742_ = lean_st_ref_get(v___y_740_);
v_env_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc_ref(v_env_743_);
lean_dec(v___x_742_);
v___x_744_ = lean_st_ref_get(v___y_738_);
v_mctx_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_mctx_745_);
lean_dec(v___x_744_);
v_lctx_746_ = lean_ctor_get(v___y_737_, 2);
v_options_747_ = lean_ctor_get(v___y_739_, 2);
lean_inc_ref(v_options_747_);
lean_inc_ref(v_lctx_746_);
v___x_748_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_748_, 0, v_env_743_);
lean_ctor_set(v___x_748_, 1, v_mctx_745_);
lean_ctor_set(v___x_748_, 2, v_lctx_746_);
lean_ctor_set(v___x_748_, 3, v_options_747_);
v___x_749_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_msgData_736_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object* v_msgData_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msgData_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_ref_764_; lean_object* v___x_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_774_; 
v_ref_764_ = lean_ctor_get(v___y_761_, 5);
v___x_765_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_774_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_inc(v_ref_764_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_ref_764_);
lean_ctor_set(v___x_770_, 1, v_a_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 1);
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg___boxed(lean_object* v_msg_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
return v_res_781_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(lean_object* v_as_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
if (lean_obj_tag(v_as_788_) == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
else
{
lean_object* v_head_796_; lean_object* v_tail_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_831_; 
v_head_796_ = lean_ctor_get(v_as_788_, 0);
v_tail_797_ = lean_ctor_get(v_as_788_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_as_788_);
if (v_isSharedCheck_831_ == 0)
{
v___x_799_ = v_as_788_;
v_isShared_800_ = v_isSharedCheck_831_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_tail_797_);
lean_inc(v_head_796_);
lean_dec(v_as_788_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_831_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_lhs_801_; lean_object* v_rhs_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_830_; 
v_lhs_801_ = lean_ctor_get(v_head_796_, 0);
v_rhs_802_ = lean_ctor_get(v_head_796_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_head_796_);
if (v_isSharedCheck_830_ == 0)
{
v___x_804_ = v_head_796_;
v_isShared_805_ = v_isSharedCheck_830_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_rhs_802_);
lean_inc(v_lhs_801_);
lean_dec(v_head_796_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_830_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; 
lean_inc_ref(v_rhs_802_);
lean_inc_ref(v_lhs_801_);
v___x_806_ = l_Lean_Meta_isExprDefEq(v_lhs_801_, v_rhs_802_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; uint8_t v___x_808_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
v___x_808_ = lean_unbox(v_a_807_);
lean_dec(v_a_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
lean_dec(v_tail_797_);
v___x_809_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1);
v___x_810_ = l_Lean_indentExpr(v_lhs_801_);
if (v_isShared_805_ == 0)
{
lean_ctor_set_tag(v___x_804_, 7);
lean_ctor_set(v___x_804_, 1, v___x_810_);
lean_ctor_set(v___x_804_, 0, v___x_809_);
v___x_812_ = v___x_804_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_820_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_800_ == 0)
{
lean_ctor_set_tag(v___x_799_, 7);
lean_ctor_set(v___x_799_, 1, v___x_813_);
lean_ctor_set(v___x_799_, 0, v___x_812_);
v___x_815_ = v___x_799_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_813_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = l_Lean_indentExpr(v_rhs_802_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_817_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
return v___x_818_;
}
}
}
else
{
lean_del_object(v___x_804_);
lean_dec_ref(v_rhs_802_);
lean_dec_ref(v_lhs_801_);
lean_del_object(v___x_799_);
v_as_788_ = v_tail_797_;
goto _start;
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_del_object(v___x_804_);
lean_dec_ref(v_rhs_802_);
lean_dec_ref(v_lhs_801_);
lean_del_object(v___x_799_);
lean_dec(v_tail_797_);
v_a_822_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_806_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_806_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___boxed(lean_object* v_as_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_as_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_838_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0));
v___x_841_ = l_Lean_stringToMessageData(v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object* v_hint_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_pattern_848_; lean_object* v_constraints_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_891_; 
v_pattern_848_ = lean_ctor_get(v_hint_842_, 0);
v_constraints_849_ = lean_ctor_get(v_hint_842_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v_hint_842_);
if (v_isSharedCheck_891_ == 0)
{
v___x_851_ = v_hint_842_;
v_isShared_852_ = v_isSharedCheck_891_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_constraints_849_);
lean_inc(v_pattern_848_);
lean_dec(v_hint_842_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_891_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; 
v___x_853_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_constraints_849_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_lhs_854_; lean_object* v_rhs_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref_known(v___x_853_, 1);
v_lhs_854_ = lean_ctor_get(v_pattern_848_, 0);
v_rhs_855_ = lean_ctor_get(v_pattern_848_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v_pattern_848_);
if (v_isSharedCheck_890_ == 0)
{
v___x_857_ = v_pattern_848_;
v_isShared_858_ = v_isSharedCheck_890_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_rhs_855_);
lean_inc(v_lhs_854_);
lean_dec(v_pattern_848_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_890_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; 
lean_inc_ref(v_rhs_855_);
lean_inc_ref(v_lhs_854_);
v___x_859_ = l_Lean_Meta_isExprDefEq(v_lhs_854_, v_rhs_855_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_881_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_881_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
uint8_t v___x_864_; 
v___x_864_ = lean_unbox(v_a_860_);
lean_dec(v_a_860_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_del_object(v___x_862_);
v___x_865_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1);
v___x_866_ = l_Lean_indentExpr(v_lhs_854_);
if (v_isShared_858_ == 0)
{
lean_ctor_set_tag(v___x_857_, 7);
lean_ctor_set(v___x_857_, 1, v___x_866_);
lean_ctor_set(v___x_857_, 0, v___x_865_);
v___x_868_ = v___x_857_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_866_);
v___x_868_ = v_reuseFailAlloc_876_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 7);
lean_ctor_set(v___x_851_, 1, v___x_869_);
lean_ctor_set(v___x_851_, 0, v___x_868_);
v___x_871_ = v___x_851_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = l_Lean_indentExpr(v_rhs_855_);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_873_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_874_;
}
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_del_object(v___x_857_);
lean_dec_ref(v_rhs_855_);
lean_dec_ref(v_lhs_854_);
lean_del_object(v___x_851_);
v___x_877_ = lean_box(0);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_877_);
v___x_879_ = v___x_862_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
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
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_del_object(v___x_857_);
lean_dec_ref(v_rhs_855_);
lean_dec_ref(v_lhs_854_);
lean_del_object(v___x_851_);
v_a_882_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_859_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_859_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
else
{
lean_del_object(v___x_851_);
lean_dec_ref(v_pattern_848_);
return v___x_853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object* v_hint_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_hint_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object* v_00_u03b1_899_, lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object* v_00_u03b1_907_, lean_object* v_msg_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(v_00_u03b1_907_, v_msg_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_914_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_915_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
return v___x_919_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_921_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
lean_ctor_set(v___x_921_, 3, v___x_920_);
lean_ctor_set(v___x_921_, 4, v___x_920_);
lean_ctor_set(v___x_921_, 5, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(lean_object* v_ext_922_, lean_object* v_b_923_, uint8_t v_kind_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_currNamespace_929_; lean_object* v___x_930_; lean_object* v_env_931_; lean_object* v_nextMacroScope_932_; lean_object* v_ngen_933_; lean_object* v_auxDeclNGen_934_; lean_object* v_traceState_935_; lean_object* v_messages_936_; lean_object* v_infoState_937_; lean_object* v_snapshotTasks_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_965_; 
v_currNamespace_929_ = lean_ctor_get(v___y_926_, 6);
v___x_930_ = lean_st_ref_take(v___y_927_);
v_env_931_ = lean_ctor_get(v___x_930_, 0);
v_nextMacroScope_932_ = lean_ctor_get(v___x_930_, 1);
v_ngen_933_ = lean_ctor_get(v___x_930_, 2);
v_auxDeclNGen_934_ = lean_ctor_get(v___x_930_, 3);
v_traceState_935_ = lean_ctor_get(v___x_930_, 4);
v_messages_936_ = lean_ctor_get(v___x_930_, 6);
v_infoState_937_ = lean_ctor_get(v___x_930_, 7);
v_snapshotTasks_938_ = lean_ctor_get(v___x_930_, 8);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v___x_930_, 5);
lean_dec(v_unused_966_);
v___x_940_ = v___x_930_;
v_isShared_941_ = v_isSharedCheck_965_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_snapshotTasks_938_);
lean_inc(v_infoState_937_);
lean_inc(v_messages_936_);
lean_inc(v_traceState_935_);
lean_inc(v_auxDeclNGen_934_);
lean_inc(v_ngen_933_);
lean_inc(v_nextMacroScope_932_);
lean_inc(v_env_931_);
lean_dec(v___x_930_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_965_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
lean_inc(v_currNamespace_929_);
v___x_942_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_931_, v_ext_922_, v_b_923_, v_kind_924_, v_currNamespace_929_);
v___x_943_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 5, v___x_943_);
lean_ctor_set(v___x_940_, 0, v___x_942_);
v___x_945_ = v___x_940_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_nextMacroScope_932_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_ngen_933_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_auxDeclNGen_934_);
lean_ctor_set(v_reuseFailAlloc_964_, 4, v_traceState_935_);
lean_ctor_set(v_reuseFailAlloc_964_, 5, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_964_, 6, v_messages_936_);
lean_ctor_set(v_reuseFailAlloc_964_, 7, v_infoState_937_);
lean_ctor_set(v_reuseFailAlloc_964_, 8, v_snapshotTasks_938_);
v___x_945_ = v_reuseFailAlloc_964_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_mctx_948_; lean_object* v_zetaDeltaFVarIds_949_; lean_object* v_postponed_950_; lean_object* v_diag_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_962_; 
v___x_946_ = lean_st_ref_set(v___y_927_, v___x_945_);
v___x_947_ = lean_st_ref_take(v___y_925_);
v_mctx_948_ = lean_ctor_get(v___x_947_, 0);
v_zetaDeltaFVarIds_949_ = lean_ctor_get(v___x_947_, 2);
v_postponed_950_ = lean_ctor_get(v___x_947_, 3);
v_diag_951_ = lean_ctor_get(v___x_947_, 4);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v___x_947_, 1);
lean_dec(v_unused_963_);
v___x_953_ = v___x_947_;
v_isShared_954_ = v_isSharedCheck_962_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_diag_951_);
lean_inc(v_postponed_950_);
lean_inc(v_zetaDeltaFVarIds_949_);
lean_inc(v_mctx_948_);
lean_dec(v___x_947_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_962_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_955_);
v___x_957_ = v___x_953_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_mctx_948_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_zetaDeltaFVarIds_949_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_postponed_950_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v_diag_951_);
v___x_957_ = v_reuseFailAlloc_961_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_st_ref_set(v___y_925_, v___x_957_);
v___x_959_ = lean_box(0);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(lean_object* v_ext_967_, lean_object* v_b_968_, lean_object* v_kind_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
uint8_t v_kind_boxed_974_; lean_object* v_res_975_; 
v_kind_boxed_974_ = lean_unbox(v_kind_969_);
v_res_975_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_967_, v_b_968_, v_kind_boxed_974_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object* v_00_u03b1_976_, lean_object* v_00_u03b2_977_, lean_object* v_00_u03c3_978_, lean_object* v_ext_979_, lean_object* v_b_980_, uint8_t v_kind_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_979_, v_b_980_, v_kind_981_, v___y_983_, v___y_984_, v___y_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object* v_00_u03b1_988_, lean_object* v_00_u03b2_989_, lean_object* v_00_u03c3_990_, lean_object* v_ext_991_, lean_object* v_b_992_, lean_object* v_kind_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
uint8_t v_kind_boxed_999_; lean_object* v_res_1000_; 
v_kind_boxed_999_ = lean_unbox(v_kind_993_);
v_res_1000_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(v_00_u03b1_988_, v_00_u03b2_989_, v_00_u03c3_990_, v_ext_991_, v_b_992_, v_kind_boxed_999_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(lean_object* v_k_1001_, uint8_t v_allowLevelAssignments_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1002_, v_k_1001_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1008_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1008_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(lean_object* v_k_1025_, lean_object* v_allowLevelAssignments_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1032_; lean_object* v_res_1033_; 
v_allowLevelAssignments_boxed_1032_ = lean_unbox(v_allowLevelAssignments_1026_);
v_res_1033_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_1025_, v_allowLevelAssignments_boxed_1032_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(lean_object* v_00_u03b1_1034_, lean_object* v_k_1035_, uint8_t v_allowLevelAssignments_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_1035_, v_allowLevelAssignments_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_k_1044_, lean_object* v_allowLevelAssignments_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1051_; lean_object* v_res_1052_; 
v_allowLevelAssignments_boxed_1051_ = lean_unbox(v_allowLevelAssignments_1045_);
v_res_1052_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(v_00_u03b1_1043_, v_k_1044_, v_allowLevelAssignments_boxed_1051_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1052_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
lean_ctor_set(v___x_1058_, 2, v___x_1057_);
lean_ctor_set(v___x_1058_, 3, v___x_1057_);
lean_ctor_set(v___x_1058_, 4, v___x_1056_);
lean_ctor_set(v___x_1058_, 5, v___x_1056_);
lean_ctor_set(v___x_1058_, 6, v___x_1056_);
lean_ctor_set(v___x_1058_, 7, v___x_1056_);
lean_ctor_set(v___x_1058_, 8, v___x_1056_);
lean_ctor_set(v___x_1058_, 9, v___x_1056_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_unsigned_to_nat(32u);
v___x_1060_ = lean_mk_empty_array_with_capacity(v___x_1059_);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1062_ = ((size_t)5ULL);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_unsigned_to_nat(32u);
v___x_1065_ = lean_mk_empty_array_with_capacity(v___x_1064_);
v___x_1066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1067_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
lean_ctor_set(v___x_1067_, 2, v___x_1063_);
lean_ctor_set(v___x_1067_, 3, v___x_1063_);
lean_ctor_set_usize(v___x_1067_, 4, v___x_1062_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1068_ = lean_box(1);
v___x_1069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1071_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1069_);
lean_ctor_set(v___x_1071_, 2, v___x_1068_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1093_, lean_object* v_declHint_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; lean_object* v_env_1098_; uint8_t v___y_1100_; uint8_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1097_ = lean_st_ref_get(v___y_1095_);
v_env_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_env_1098_);
lean_dec(v___x_1097_);
v___x_1156_ = l_Lean_Name_isAnonymous(v_declHint_1094_);
v___x_1157_ = lean_bool_not(v___x_1156_);
if (v___x_1157_ == 0)
{
v___y_1100_ = v___x_1157_;
goto v___jp_1099_;
}
else
{
uint8_t v_isExporting_1158_; 
v_isExporting_1158_ = lean_ctor_get_uint8(v_env_1098_, sizeof(void*)*8);
v___y_1100_ = v_isExporting_1158_;
goto v___jp_1099_;
}
v___jp_1099_:
{
if (v___y_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_dec_ref(v_env_1098_);
lean_dec(v_declHint_1094_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_msg_1093_);
return v___x_1101_;
}
else
{
uint8_t v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1102_ = 0;
lean_inc_ref(v_env_1098_);
v___x_1103_ = l_Lean_Environment_setExporting(v_env_1098_, v___x_1102_);
lean_inc(v_declHint_1094_);
lean_inc_ref(v___x_1103_);
v___x_1104_ = l_Lean_Environment_contains(v___x_1103_, v_declHint_1094_, v___y_1100_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
lean_dec_ref(v___x_1103_);
lean_dec_ref(v_env_1098_);
lean_dec(v_declHint_1094_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_msg_1093_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_c_1111_; lean_object* v___x_1112_; 
v___x_1106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1108_ = l_Lean_Options_empty;
v___x_1109_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1103_);
lean_ctor_set(v___x_1109_, 1, v___x_1106_);
lean_ctor_set(v___x_1109_, 2, v___x_1107_);
lean_ctor_set(v___x_1109_, 3, v___x_1108_);
lean_inc(v_declHint_1094_);
v___x_1110_ = l_Lean_MessageData_ofConstName(v_declHint_1094_, v___x_1102_);
v_c_1111_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1111_, 0, v___x_1109_);
lean_ctor_set(v_c_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1098_, v_declHint_1094_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v_env_1098_);
lean_dec(v_declHint_1094_);
v___x_1113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_c_1111_);
v___x_1115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_MessageData_note(v___x_1116_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_msg_1093_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
else
{
lean_object* v_val_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1155_; 
v_val_1120_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1122_ = v___x_1112_;
v_isShared_1123_ = v_isSharedCheck_1155_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_val_1120_);
lean_dec(v___x_1112_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1155_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_mod_1127_; uint8_t v___x_1128_; 
v___x_1124_ = lean_box(0);
v___x_1125_ = l_Lean_Environment_header(v_env_1098_);
lean_dec_ref(v_env_1098_);
v___x_1126_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1125_);
v_mod_1127_ = lean_array_get(v___x_1124_, v___x_1126_, v_val_1120_);
lean_dec(v_val_1120_);
lean_dec_ref(v___x_1126_);
v___x_1128_ = l_Lean_isPrivateName(v_declHint_1094_);
lean_dec(v_declHint_1094_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v_c_1111_);
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_MessageData_ofName(v_mod_1127_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_MessageData_note(v___x_1136_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_msg_1093_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1138_);
v___x_1140_ = v___x_1122_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_c_1111_);
v___x_1144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_MessageData_ofName(v_mod_1127_);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_MessageData_note(v___x_1149_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_msg_1093_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1151_);
v___x_1153_ = v___x_1122_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1159_, lean_object* v_declHint_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1159_, v_declHint_1160_, v___y_1161_);
lean_dec(v___y_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object* v_msg_1164_, lean_object* v_declHint_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1181_; 
v___x_1171_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1164_, v_declHint_1165_, v___y_1169_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1176_ = l_Lean_unknownIdentifierMessageTag;
v___x_1177_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v_a_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1182_, lean_object* v_declHint_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1182_, v_declHint_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1190_, lean_object* v_msg_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_fileName_1197_; lean_object* v_fileMap_1198_; lean_object* v_options_1199_; lean_object* v_currRecDepth_1200_; lean_object* v_maxRecDepth_1201_; lean_object* v_ref_1202_; lean_object* v_currNamespace_1203_; lean_object* v_openDecls_1204_; lean_object* v_initHeartbeats_1205_; lean_object* v_maxHeartbeats_1206_; lean_object* v_quotContext_1207_; lean_object* v_currMacroScope_1208_; uint8_t v_diag_1209_; lean_object* v_cancelTk_x3f_1210_; uint8_t v_suppressElabErrors_1211_; lean_object* v_inheritedTraceOptions_1212_; lean_object* v_ref_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_fileName_1197_ = lean_ctor_get(v___y_1194_, 0);
v_fileMap_1198_ = lean_ctor_get(v___y_1194_, 1);
v_options_1199_ = lean_ctor_get(v___y_1194_, 2);
v_currRecDepth_1200_ = lean_ctor_get(v___y_1194_, 3);
v_maxRecDepth_1201_ = lean_ctor_get(v___y_1194_, 4);
v_ref_1202_ = lean_ctor_get(v___y_1194_, 5);
v_currNamespace_1203_ = lean_ctor_get(v___y_1194_, 6);
v_openDecls_1204_ = lean_ctor_get(v___y_1194_, 7);
v_initHeartbeats_1205_ = lean_ctor_get(v___y_1194_, 8);
v_maxHeartbeats_1206_ = lean_ctor_get(v___y_1194_, 9);
v_quotContext_1207_ = lean_ctor_get(v___y_1194_, 10);
v_currMacroScope_1208_ = lean_ctor_get(v___y_1194_, 11);
v_diag_1209_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*14);
v_cancelTk_x3f_1210_ = lean_ctor_get(v___y_1194_, 12);
v_suppressElabErrors_1211_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1212_ = lean_ctor_get(v___y_1194_, 13);
v_ref_1213_ = l_Lean_replaceRef(v_ref_1190_, v_ref_1202_);
lean_inc_ref(v_inheritedTraceOptions_1212_);
lean_inc(v_cancelTk_x3f_1210_);
lean_inc(v_currMacroScope_1208_);
lean_inc(v_quotContext_1207_);
lean_inc(v_maxHeartbeats_1206_);
lean_inc(v_initHeartbeats_1205_);
lean_inc(v_openDecls_1204_);
lean_inc(v_currNamespace_1203_);
lean_inc(v_maxRecDepth_1201_);
lean_inc(v_currRecDepth_1200_);
lean_inc_ref(v_options_1199_);
lean_inc_ref(v_fileMap_1198_);
lean_inc_ref(v_fileName_1197_);
v___x_1214_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1214_, 0, v_fileName_1197_);
lean_ctor_set(v___x_1214_, 1, v_fileMap_1198_);
lean_ctor_set(v___x_1214_, 2, v_options_1199_);
lean_ctor_set(v___x_1214_, 3, v_currRecDepth_1200_);
lean_ctor_set(v___x_1214_, 4, v_maxRecDepth_1201_);
lean_ctor_set(v___x_1214_, 5, v_ref_1213_);
lean_ctor_set(v___x_1214_, 6, v_currNamespace_1203_);
lean_ctor_set(v___x_1214_, 7, v_openDecls_1204_);
lean_ctor_set(v___x_1214_, 8, v_initHeartbeats_1205_);
lean_ctor_set(v___x_1214_, 9, v_maxHeartbeats_1206_);
lean_ctor_set(v___x_1214_, 10, v_quotContext_1207_);
lean_ctor_set(v___x_1214_, 11, v_currMacroScope_1208_);
lean_ctor_set(v___x_1214_, 12, v_cancelTk_x3f_1210_);
lean_ctor_set(v___x_1214_, 13, v_inheritedTraceOptions_1212_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*14, v_diag_1209_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*14 + 1, v_suppressElabErrors_1211_);
v___x_1215_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_1191_, v___y_1192_, v___y_1193_, v___x_1214_, v___y_1195_);
lean_dec_ref_known(v___x_1214_, 14);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1216_, lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1216_, v_msg_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v_ref_1216_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_ref_1224_, lean_object* v_msg_1225_, lean_object* v_declHint_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; 
v___x_1232_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1225_, v_declHint_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1224_, v_a_1233_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1235_, lean_object* v_msg_1236_, lean_object* v_declHint_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1235_, v_msg_1236_, v_declHint_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v_ref_1235_);
return v_res_1243_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1246_ = l_Lean_stringToMessageData(v___x_1245_);
return v___x_1246_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1249_ = l_Lean_stringToMessageData(v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1250_, lean_object* v_constName_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1257_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1258_ = 0;
lean_inc(v_constName_1251_);
v___x_1259_ = l_Lean_MessageData_ofConstName(v_constName_1251_, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1257_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1250_, v___x_1262_, v_constName_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1264_, lean_object* v_constName_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1264_, v_constName_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v_ref_1264_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(lean_object* v_constName_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_ref_1278_; lean_object* v___x_1279_; 
v_ref_1278_ = lean_ctor_get(v___y_1275_, 5);
v___x_1279_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1278_, v_constName_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(lean_object* v_constName_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v_env_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1293_ = lean_st_ref_get(v___y_1291_);
v_env_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc_ref(v_env_1294_);
lean_dec(v___x_1293_);
v___x_1295_ = 0;
lean_inc(v_constName_1287_);
v___x_1296_ = l_Lean_Environment_find_x3f(v_env_1294_, v_constName_1287_, v___x_1295_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v___x_1297_;
}
else
{
lean_object* v_val_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_constName_1287_);
v_val_1298_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1296_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_val_1298_);
lean_dec(v___x_1296_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 0);
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_val_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(lean_object* v_constName_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_constName_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
return v_res_1312_;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_Meta_addUnificationHint___lam__0___closed__0));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object* v_declName_1316_, uint8_t v_kind_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
lean_inc(v_declName_1316_);
v___x_1323_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_declName_1316_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v___x_1325_ = 0;
v___x_1326_ = l_Lean_ConstantInfo_value_x3f(v_a_1324_, v___x_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec(v_declName_1316_);
v___x_1327_ = lean_obj_once(&l_Lean_Meta_addUnificationHint___lam__0___closed__1, &l_Lean_Meta_addUnificationHint___lam__0___closed__1_once, _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1);
v___x_1328_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_1327_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
return v___x_1328_;
}
else
{
lean_object* v_val_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_val_1329_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_val_1329_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1330_ = lean_box(0);
v___x_1331_ = l_Lean_Meta_lambdaMetaTelescope(v_val_1329_, v___x_1330_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v_val_1329_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v_snd_1333_; lean_object* v_snd_1334_; lean_object* v___x_1335_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
v_snd_1333_ = lean_ctor_get(v_a_1332_, 1);
lean_inc(v_snd_1333_);
lean_dec(v_a_1332_);
v_snd_1334_ = lean_ctor_get(v_snd_1333_, 1);
lean_inc(v_snd_1334_);
lean_dec(v_snd_1333_);
v___x_1335_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; 
lean_dec(v_declName_1316_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_a_1336_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
return v___x_1337_;
}
else
{
lean_object* v_a_1338_; lean_object* v_pattern_1339_; lean_object* v_lhs_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1375_; 
v_a_1338_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1335_, 1);
v_pattern_1339_ = lean_ctor_get(v_a_1338_, 0);
lean_inc_ref(v_pattern_1339_);
v_lhs_1340_ = lean_ctor_get(v_pattern_1339_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_pattern_1339_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v_pattern_1339_, 1);
lean_dec(v_unused_1376_);
v___x_1342_ = v_pattern_1339_;
v_isShared_1343_ = v_isSharedCheck_1375_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_lhs_1340_);
lean_dec(v_pattern_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1375_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v_config_1345_; uint8_t v_trackZetaDelta_1346_; lean_object* v_zetaDeltaSet_1347_; lean_object* v_lctx_1348_; lean_object* v_localInstances_1349_; lean_object* v_defEqCtx_x3f_1350_; lean_object* v_synthPendingDepth_1351_; lean_object* v_canUnfold_x3f_1352_; uint8_t v_univApprox_1353_; uint8_t v_inTypeClassResolution_1354_; uint8_t v_cacheInferType_1355_; uint64_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1344_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_1345_ = lean_ctor_get(v___x_1344_, 0);
v_trackZetaDelta_1346_ = lean_ctor_get_uint8(v___y_1318_, sizeof(void*)*7);
v_zetaDeltaSet_1347_ = lean_ctor_get(v___y_1318_, 1);
v_lctx_1348_ = lean_ctor_get(v___y_1318_, 2);
v_localInstances_1349_ = lean_ctor_get(v___y_1318_, 3);
v_defEqCtx_x3f_1350_ = lean_ctor_get(v___y_1318_, 4);
v_synthPendingDepth_1351_ = lean_ctor_get(v___y_1318_, 5);
v_canUnfold_x3f_1352_ = lean_ctor_get(v___y_1318_, 6);
v_univApprox_1353_ = lean_ctor_get_uint8(v___y_1318_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1354_ = lean_ctor_get_uint8(v___y_1318_, sizeof(void*)*7 + 2);
v_cacheInferType_1355_ = lean_ctor_get_uint8(v___y_1318_, sizeof(void*)*7 + 3);
v___x_1356_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1345_);
lean_inc_ref(v_config_1345_);
v___x_1357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1357_, 0, v_config_1345_);
lean_ctor_set_uint64(v___x_1357_, sizeof(void*)*1, v___x_1356_);
lean_inc(v_canUnfold_x3f_1352_);
lean_inc(v_synthPendingDepth_1351_);
lean_inc(v_defEqCtx_x3f_1350_);
lean_inc_ref(v_localInstances_1349_);
lean_inc_ref(v_lctx_1348_);
lean_inc(v_zetaDeltaSet_1347_);
v___x_1358_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v_zetaDeltaSet_1347_);
lean_ctor_set(v___x_1358_, 2, v_lctx_1348_);
lean_ctor_set(v___x_1358_, 3, v_localInstances_1349_);
lean_ctor_set(v___x_1358_, 4, v_defEqCtx_x3f_1350_);
lean_ctor_set(v___x_1358_, 5, v_synthPendingDepth_1351_);
lean_ctor_set(v___x_1358_, 6, v_canUnfold_x3f_1352_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7, v_trackZetaDelta_1346_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7 + 1, v_univApprox_1353_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1354_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7 + 3, v_cacheInferType_1355_);
v___x_1359_ = l_Lean_Meta_DiscrTree_mkPath(v_lhs_1340_, v___x_1325_, v___x_1358_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec_ref_known(v___x_1358_, 7);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_a_1338_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
lean_dec_ref_known(v___x_1361_, 1);
v___x_1362_ = l_Lean_Meta_unificationHintExtension;
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_declName_1316_);
lean_ctor_set(v___x_1342_, 0, v_a_1360_);
v___x_1364_ = v___x_1342_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_declName_1316_);
v___x_1364_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v___x_1362_, v___x_1364_, v_kind_1317_, v___y_1319_, v___y_1320_, v___y_1321_);
return v___x_1365_;
}
}
else
{
lean_dec(v_a_1360_);
lean_del_object(v___x_1342_);
lean_dec(v_declName_1316_);
return v___x_1361_;
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_del_object(v___x_1342_);
lean_dec(v_a_1338_);
lean_dec(v_declName_1316_);
v_a_1367_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1359_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1359_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_declName_1316_);
v_a_1377_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1331_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1331_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_declName_1316_);
v_a_1385_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1323_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1323_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object* v_declName_1393_, lean_object* v_kind_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v_kind_boxed_1400_; lean_object* v_res_1401_; 
v_kind_boxed_1400_ = lean_unbox(v_kind_1394_);
v_res_1401_ = l_Lean_Meta_addUnificationHint___lam__0(v_declName_1393_, v_kind_boxed_1400_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* v_declName_1402_, uint8_t v_kind_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v___f_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_box(v_kind_1403_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1410_, 0, v_declName_1402_);
lean_closure_set(v___f_1410_, 1, v___x_1409_);
v___x_1411_ = 0;
v___x_1412_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v___f_1410_, v___x_1411_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* v_declName_1413_, lean_object* v_kind_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
uint8_t v_kind_boxed_1420_; lean_object* v_res_1421_; 
v_kind_boxed_1420_ = lean_unbox(v_kind_1414_);
v_res_1421_ = l_Lean_Meta_addUnificationHint(v_declName_1413_, v_kind_boxed_1420_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object* v_00_u03b1_1422_, lean_object* v_constName_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1430_, lean_object* v_constName_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(v_00_u03b1_1430_, v_constName_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1438_, lean_object* v_ref_1439_, lean_object* v_constName_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1439_, v_constName_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1447_, lean_object* v_ref_1448_, lean_object* v_constName_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(v_00_u03b1_1447_, v_ref_1448_, v_constName_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v_ref_1448_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_1456_, lean_object* v_ref_1457_, lean_object* v_msg_1458_, lean_object* v_declHint_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1457_, v_msg_1458_, v_declHint_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1466_, lean_object* v_ref_1467_, lean_object* v_msg_1468_, lean_object* v_declHint_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(v_00_u03b1_1466_, v_ref_1467_, v_msg_1468_, v_declHint_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v_ref_1467_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1476_, lean_object* v_declHint_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1476_, v_declHint_1477_, v___y_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1484_, lean_object* v_declHint_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(v_msg_1484_, v_declHint_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1492_, lean_object* v_ref_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1493_, v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_ref_1502_, lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(v_00_u03b1_1501_, v_ref_1502_, v_msg_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v_ref_1502_);
return v_res_1509_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1516_; uint64_t v___x_1517_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1517_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1519_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1520_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set_uint64(v___x_1520_, sizeof(void*)*1, v___x_1518_);
return v___x_1520_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1521_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1525_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
lean_ctor_set(v___x_1525_, 2, v___x_1524_);
lean_ctor_set(v___x_1525_, 3, v___x_1524_);
lean_ctor_set(v___x_1525_, 4, v___x_1524_);
lean_ctor_set(v___x_1525_, 5, v___x_1524_);
return v___x_1525_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
lean_ctor_set(v___x_1527_, 2, v___x_1526_);
lean_ctor_set(v___x_1527_, 3, v___x_1526_);
lean_ctor_set(v___x_1527_, 4, v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v_declName_1530_, lean_object* v_stx_1531_, uint8_t v_kind_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1531_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1536_) == 0)
{
uint8_t v___x_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; size_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref_known(v___x_1536_, 1);
v___x_1537_ = 0;
v___x_1538_ = 1;
v___x_1539_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1540_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1541_ = lean_unsigned_to_nat(32u);
v___x_1542_ = lean_mk_empty_array_with_capacity(v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1544_ = ((size_t)5ULL);
lean_inc_n(v___x_1528_, 6);
v___x_1545_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1542_);
lean_ctor_set(v___x_1545_, 2, v___x_1528_);
lean_ctor_set(v___x_1545_, 3, v___x_1528_);
lean_ctor_set_usize(v___x_1545_, 4, v___x_1544_);
v___x_1546_ = lean_box(1);
lean_inc_ref(v___x_1545_);
v___x_1547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1540_);
lean_ctor_set(v___x_1547_, 1, v___x_1545_);
lean_ctor_set(v___x_1547_, 2, v___x_1546_);
v___x_1548_ = lean_mk_empty_array_with_capacity(v___x_1528_);
v___x_1549_ = lean_box(0);
lean_inc(v___x_1529_);
v___x_1550_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1550_, 0, v___x_1539_);
lean_ctor_set(v___x_1550_, 1, v___x_1529_);
lean_ctor_set(v___x_1550_, 2, v___x_1547_);
lean_ctor_set(v___x_1550_, 3, v___x_1548_);
lean_ctor_set(v___x_1550_, 4, v___x_1549_);
lean_ctor_set(v___x_1550_, 5, v___x_1528_);
lean_ctor_set(v___x_1550_, 6, v___x_1549_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*7, v___x_1537_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*7 + 1, v___x_1537_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*7 + 2, v___x_1537_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*7 + 3, v___x_1538_);
v___x_1551_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1528_);
lean_ctor_set(v___x_1551_, 1, v___x_1528_);
lean_ctor_set(v___x_1551_, 2, v___x_1528_);
lean_ctor_set(v___x_1551_, 3, v___x_1528_);
lean_ctor_set(v___x_1551_, 4, v___x_1540_);
lean_ctor_set(v___x_1551_, 5, v___x_1540_);
lean_ctor_set(v___x_1551_, 6, v___x_1540_);
lean_ctor_set(v___x_1551_, 7, v___x_1540_);
lean_ctor_set(v___x_1551_, 8, v___x_1540_);
lean_ctor_set(v___x_1551_, 9, v___x_1540_);
v___x_1552_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1553_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1551_);
lean_ctor_set(v___x_1554_, 1, v___x_1552_);
lean_ctor_set(v___x_1554_, 2, v___x_1529_);
lean_ctor_set(v___x_1554_, 3, v___x_1545_);
lean_ctor_set(v___x_1554_, 4, v___x_1553_);
v___x_1555_ = lean_st_mk_ref(v___x_1554_);
v___x_1556_ = l_Lean_Meta_addUnificationHint(v_declName_1530_, v_kind_1532_, v___x_1550_, v___x_1555_, v___y_1533_, v___y_1534_);
lean_dec_ref_known(v___x_1550_, 7);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1565_; 
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v___x_1556_, 0);
lean_dec(v_unused_1566_);
v___x_1558_ = v___x_1556_;
v_isShared_1559_ = v_isSharedCheck_1565_;
goto v_resetjp_1557_;
}
else
{
lean_dec(v___x_1556_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1565_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1560_ = lean_st_ref_get(v___x_1555_);
lean_dec(v___x_1555_);
lean_dec(v___x_1560_);
v___x_1561_ = lean_box(0);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1561_);
v___x_1563_ = v___x_1558_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_dec(v___x_1555_);
return v___x_1556_;
}
}
else
{
lean_dec(v_declName_1530_);
lean_dec(v___x_1529_);
lean_dec(v___x_1528_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1567_, lean_object* v___x_1568_, lean_object* v_declName_1569_, lean_object* v_stx_1570_, lean_object* v_kind_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_kind_boxed_1575_; lean_object* v_res_1576_; 
v_kind_boxed_1575_ = lean_unbox(v_kind_1571_);
v_res_1576_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1567_, v___x_1568_, v_declName_1569_, v_stx_1570_, v_kind_boxed_1575_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v_env_1582_; lean_object* v_options_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1581_ = lean_st_ref_get(v___y_1579_);
v_env_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc_ref(v_env_1582_);
lean_dec(v___x_1581_);
v_options_1583_ = lean_ctor_get(v___y_1578_, 2);
v___x_1584_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1585_ = lean_unsigned_to_nat(32u);
v___x_1586_ = lean_mk_empty_array_with_capacity(v___x_1585_);
lean_dec_ref(v___x_1586_);
v___x_1587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_1583_);
v___x_1588_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1588_, 0, v_env_1582_);
lean_ctor_set(v___x_1588_, 1, v___x_1584_);
lean_ctor_set(v___x_1588_, 2, v___x_1587_);
lean_ctor_set(v___x_1588_, 3, v_options_1583_);
v___x_1589_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v_msgData_1577_);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_ref_1600_; lean_object* v___x_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1610_; 
v_ref_1600_ = lean_ctor_get(v___y_1597_, 5);
v___x_1601_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msg_1596_, v___y_1597_, v___y_1598_);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
lean_inc(v_ref_1600_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v_ref_1600_);
lean_ctor_set(v___x_1606_, 1, v_a_1602_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 1);
lean_ctor_set(v___x_1604_, 0, v___x_1606_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
return v_res_1615_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1618_ = l_Lean_stringToMessageData(v___x_1617_);
return v___x_1618_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1621_ = l_Lean_stringToMessageData(v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1622_, lean_object* v_decl_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1627_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1628_ = l_Lean_MessageData_ofName(v___x_1622_);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v___x_1631_, v___y_1624_, v___y_1625_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1633_, lean_object* v_decl_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1633_, v_decl_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v_decl_1634_);
return v_res_1638_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_unsigned_to_nat(3033092106u);
v___x_1683_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1684_ = l_Lean_Name_num___override(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1687_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1688_ = l_Lean_Name_str___override(v___x_1687_, v___x_1686_);
return v___x_1688_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1691_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1692_ = l_Lean_Name_str___override(v___x_1691_, v___x_1690_);
return v___x_1692_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = lean_unsigned_to_nat(2u);
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1695_ = l_Lean_Name_num___override(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1702_ = 0;
v___x_1703_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1704_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1705_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1706_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v___x_1704_);
lean_ctor_set(v___x_1706_, 2, v___x_1703_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*3, v___x_1702_);
return v___x_1706_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___f_1707_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___f_1708_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1709_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v___f_1708_);
lean_ctor_set(v___x_1710_, 2, v___f_1707_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1713_ = l_Lean_registerBuiltinAttribute(v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1716_, lean_object* v_msg_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1717_, v___y_1718_, v___y_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_msg_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(v_00_u03b1_1722_, v_msg_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1727_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0(void){
_start:
{
uint8_t v___x_1728_; uint64_t v___x_1729_; 
v___x_1728_ = 2;
v___x_1729_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* v_p_1730_, lean_object* v_e_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v___x_1737_; uint8_t v_foApprox_1738_; uint8_t v_ctxApprox_1739_; uint8_t v_quasiPatternApprox_1740_; uint8_t v_constApprox_1741_; uint8_t v_isDefEqStuckEx_1742_; uint8_t v_unificationHints_1743_; uint8_t v_proofIrrelevance_1744_; uint8_t v_assignSyntheticOpaque_1745_; uint8_t v_offsetCnstrs_1746_; uint8_t v_etaStruct_1747_; uint8_t v_univApprox_1748_; uint8_t v_iota_1749_; uint8_t v_beta_1750_; uint8_t v_proj_1751_; uint8_t v_zeta_1752_; uint8_t v_zetaDelta_1753_; uint8_t v_zetaUnused_1754_; uint8_t v_zetaHave_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1782_; 
v___x_1737_ = l_Lean_Meta_Context_config(v_a_1732_);
v_foApprox_1738_ = lean_ctor_get_uint8(v___x_1737_, 0);
v_ctxApprox_1739_ = lean_ctor_get_uint8(v___x_1737_, 1);
v_quasiPatternApprox_1740_ = lean_ctor_get_uint8(v___x_1737_, 2);
v_constApprox_1741_ = lean_ctor_get_uint8(v___x_1737_, 3);
v_isDefEqStuckEx_1742_ = lean_ctor_get_uint8(v___x_1737_, 4);
v_unificationHints_1743_ = lean_ctor_get_uint8(v___x_1737_, 5);
v_proofIrrelevance_1744_ = lean_ctor_get_uint8(v___x_1737_, 6);
v_assignSyntheticOpaque_1745_ = lean_ctor_get_uint8(v___x_1737_, 7);
v_offsetCnstrs_1746_ = lean_ctor_get_uint8(v___x_1737_, 8);
v_etaStruct_1747_ = lean_ctor_get_uint8(v___x_1737_, 10);
v_univApprox_1748_ = lean_ctor_get_uint8(v___x_1737_, 11);
v_iota_1749_ = lean_ctor_get_uint8(v___x_1737_, 12);
v_beta_1750_ = lean_ctor_get_uint8(v___x_1737_, 13);
v_proj_1751_ = lean_ctor_get_uint8(v___x_1737_, 14);
v_zeta_1752_ = lean_ctor_get_uint8(v___x_1737_, 15);
v_zetaDelta_1753_ = lean_ctor_get_uint8(v___x_1737_, 16);
v_zetaUnused_1754_ = lean_ctor_get_uint8(v___x_1737_, 17);
v_zetaHave_1755_ = lean_ctor_get_uint8(v___x_1737_, 18);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1757_ = v___x_1737_;
v_isShared_1758_ = v_isSharedCheck_1782_;
goto v_resetjp_1756_;
}
else
{
lean_dec(v___x_1737_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1782_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
uint8_t v_trackZetaDelta_1759_; lean_object* v_zetaDeltaSet_1760_; lean_object* v_lctx_1761_; lean_object* v_localInstances_1762_; lean_object* v_defEqCtx_x3f_1763_; lean_object* v_synthPendingDepth_1764_; lean_object* v_canUnfold_x3f_1765_; uint8_t v_univApprox_1766_; uint8_t v_inTypeClassResolution_1767_; uint8_t v_cacheInferType_1768_; uint8_t v___x_1769_; lean_object* v_config_1771_; 
v_trackZetaDelta_1759_ = lean_ctor_get_uint8(v_a_1732_, sizeof(void*)*7);
v_zetaDeltaSet_1760_ = lean_ctor_get(v_a_1732_, 1);
v_lctx_1761_ = lean_ctor_get(v_a_1732_, 2);
v_localInstances_1762_ = lean_ctor_get(v_a_1732_, 3);
v_defEqCtx_x3f_1763_ = lean_ctor_get(v_a_1732_, 4);
v_synthPendingDepth_1764_ = lean_ctor_get(v_a_1732_, 5);
v_canUnfold_x3f_1765_ = lean_ctor_get(v_a_1732_, 6);
v_univApprox_1766_ = lean_ctor_get_uint8(v_a_1732_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1767_ = lean_ctor_get_uint8(v_a_1732_, sizeof(void*)*7 + 2);
v_cacheInferType_1768_ = lean_ctor_get_uint8(v_a_1732_, sizeof(void*)*7 + 3);
v___x_1769_ = 2;
if (v_isShared_1758_ == 0)
{
v_config_1771_ = v___x_1757_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 0, v_foApprox_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 1, v_ctxApprox_1739_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 2, v_quasiPatternApprox_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 3, v_constApprox_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 4, v_isDefEqStuckEx_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 5, v_unificationHints_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 6, v_proofIrrelevance_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 7, v_assignSyntheticOpaque_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 8, v_offsetCnstrs_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 10, v_etaStruct_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 11, v_univApprox_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 12, v_iota_1749_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 13, v_beta_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 14, v_proj_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 15, v_zeta_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 16, v_zetaDelta_1753_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 17, v_zetaUnused_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, 18, v_zetaHave_1755_);
v_config_1771_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
uint64_t v___x_1772_; uint64_t v___x_1773_; uint64_t v___x_1774_; uint64_t v___x_1775_; uint64_t v___x_1776_; uint64_t v_key_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_ctor_set_uint8(v_config_1771_, 9, v___x_1769_);
v___x_1772_ = l_Lean_Meta_Context_configKey(v_a_1732_);
v___x_1773_ = 3ULL;
v___x_1774_ = lean_uint64_shift_right(v___x_1772_, v___x_1773_);
v___x_1775_ = lean_uint64_shift_left(v___x_1774_, v___x_1773_);
v___x_1776_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0);
v_key_1777_ = lean_uint64_lor(v___x_1775_, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1778_, 0, v_config_1771_);
lean_ctor_set_uint64(v___x_1778_, sizeof(void*)*1, v_key_1777_);
lean_inc(v_canUnfold_x3f_1765_);
lean_inc(v_synthPendingDepth_1764_);
lean_inc(v_defEqCtx_x3f_1763_);
lean_inc_ref(v_localInstances_1762_);
lean_inc_ref(v_lctx_1761_);
lean_inc(v_zetaDeltaSet_1760_);
v___x_1779_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_zetaDeltaSet_1760_);
lean_ctor_set(v___x_1779_, 2, v_lctx_1761_);
lean_ctor_set(v___x_1779_, 3, v_localInstances_1762_);
lean_ctor_set(v___x_1779_, 4, v_defEqCtx_x3f_1763_);
lean_ctor_set(v___x_1779_, 5, v_synthPendingDepth_1764_);
lean_ctor_set(v___x_1779_, 6, v_canUnfold_x3f_1765_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*7, v_trackZetaDelta_1759_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*7 + 1, v_univApprox_1766_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1767_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*7 + 3, v_cacheInferType_1768_);
lean_inc(v_a_1735_);
lean_inc_ref(v_a_1734_);
lean_inc(v_a_1733_);
v___x_1780_ = lean_is_expr_def_eq(v_p_1730_, v_e_1731_, v___x_1779_, v_a_1733_, v_a_1734_, v_a_1735_);
return v___x_1780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object* v_p_1783_, lean_object* v_e_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_p_1783_, v_e_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1790_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = lean_unsigned_to_nat(32u);
v___x_1792_ = lean_mk_empty_array_with_capacity(v___x_1791_);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1794_ = ((size_t)5ULL);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_unsigned_to_nat(32u);
v___x_1797_ = lean_mk_empty_array_with_capacity(v___x_1796_);
v___x_1798_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__0);
v___x_1799_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___x_1797_);
lean_ctor_set(v___x_1799_, 2, v___x_1795_);
lean_ctor_set(v___x_1799_, 3, v___x_1795_);
lean_ctor_set_usize(v___x_1799_, 4, v___x_1794_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg(lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; lean_object* v_traceState_1803_; lean_object* v_traces_1804_; lean_object* v___x_1805_; lean_object* v_traceState_1806_; lean_object* v_env_1807_; lean_object* v_nextMacroScope_1808_; lean_object* v_ngen_1809_; lean_object* v_auxDeclNGen_1810_; lean_object* v_cache_1811_; lean_object* v_messages_1812_; lean_object* v_infoState_1813_; lean_object* v_snapshotTasks_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1833_; 
v___x_1802_ = lean_st_ref_get(v___y_1800_);
v_traceState_1803_ = lean_ctor_get(v___x_1802_, 4);
lean_inc_ref(v_traceState_1803_);
lean_dec(v___x_1802_);
v_traces_1804_ = lean_ctor_get(v_traceState_1803_, 0);
lean_inc_ref(v_traces_1804_);
lean_dec_ref(v_traceState_1803_);
v___x_1805_ = lean_st_ref_take(v___y_1800_);
v_traceState_1806_ = lean_ctor_get(v___x_1805_, 4);
v_env_1807_ = lean_ctor_get(v___x_1805_, 0);
v_nextMacroScope_1808_ = lean_ctor_get(v___x_1805_, 1);
v_ngen_1809_ = lean_ctor_get(v___x_1805_, 2);
v_auxDeclNGen_1810_ = lean_ctor_get(v___x_1805_, 3);
v_cache_1811_ = lean_ctor_get(v___x_1805_, 5);
v_messages_1812_ = lean_ctor_get(v___x_1805_, 6);
v_infoState_1813_ = lean_ctor_get(v___x_1805_, 7);
v_snapshotTasks_1814_ = lean_ctor_get(v___x_1805_, 8);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1816_ = v___x_1805_;
v_isShared_1817_ = v_isSharedCheck_1833_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_snapshotTasks_1814_);
lean_inc(v_infoState_1813_);
lean_inc(v_messages_1812_);
lean_inc(v_cache_1811_);
lean_inc(v_traceState_1806_);
lean_inc(v_auxDeclNGen_1810_);
lean_inc(v_ngen_1809_);
lean_inc(v_nextMacroScope_1808_);
lean_inc(v_env_1807_);
lean_dec(v___x_1805_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1833_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
uint64_t v_tid_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1831_; 
v_tid_1818_ = lean_ctor_get_uint64(v_traceState_1806_, sizeof(void*)*1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_traceState_1806_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v_traceState_1806_, 0);
lean_dec(v_unused_1832_);
v___x_1820_ = v_traceState_1806_;
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v_traceState_1806_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___closed__1);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1822_);
v___x_1824_ = v___x_1820_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1822_);
lean_ctor_set_uint64(v_reuseFailAlloc_1830_, sizeof(void*)*1, v_tid_1818_);
v___x_1824_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 4, v___x_1824_);
v___x_1826_ = v___x_1816_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_env_1807_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_nextMacroScope_1808_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_ngen_1809_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_auxDeclNGen_1810_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1829_, 5, v_cache_1811_);
lean_ctor_set(v_reuseFailAlloc_1829_, 6, v_messages_1812_);
lean_ctor_set(v_reuseFailAlloc_1829_, 7, v_infoState_1813_);
lean_ctor_set(v_reuseFailAlloc_1829_, 8, v_snapshotTasks_1814_);
v___x_1826_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_st_ref_set(v___y_1800_, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_traces_1804_);
return v___x_1828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg___boxed(lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg(v___y_1834_);
lean_dec(v___y_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg(v___y_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object* v_opts_1849_, lean_object* v_opt_1850_){
_start:
{
lean_object* v_name_1851_; lean_object* v_defValue_1852_; lean_object* v_map_1853_; lean_object* v___x_1854_; 
v_name_1851_ = lean_ctor_get(v_opt_1850_, 0);
v_defValue_1852_ = lean_ctor_get(v_opt_1850_, 1);
v_map_1853_ = lean_ctor_get(v_opts_1849_, 0);
v___x_1854_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1853_, v_name_1851_);
if (lean_obj_tag(v___x_1854_) == 0)
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_unbox(v_defValue_1852_);
return v___x_1855_;
}
else
{
lean_object* v_val_1856_; 
v_val_1856_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_val_1856_);
lean_dec_ref_known(v___x_1854_, 1);
if (lean_obj_tag(v_val_1856_) == 1)
{
uint8_t v_v_1857_; 
v_v_1857_ = lean_ctor_get_uint8(v_val_1856_, 0);
lean_dec_ref_known(v_val_1856_, 0);
return v_v_1857_;
}
else
{
uint8_t v___x_1858_; 
lean_dec(v_val_1856_);
v___x_1858_ = lean_unbox(v_defValue_1852_);
return v___x_1858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object* v_opts_1859_, lean_object* v_opt_1860_){
_start:
{
uint8_t v_res_1861_; lean_object* v_r_1862_; 
v_res_1861_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v_opts_1859_, v_opt_1860_);
lean_dec_ref(v_opt_1860_);
lean_dec_ref(v_opts_1859_);
v_r_1862_ = lean_box(v_res_1861_);
return v_r_1862_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
if (lean_obj_tag(v_x_1863_) == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = l_List_reverse___redArg(v_x_1864_);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
else
{
lean_object* v_tail_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1890_; 
v_tail_1872_ = lean_ctor_get(v_x_1863_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_x_1863_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; 
v_unused_1891_ = lean_ctor_get(v_x_1863_, 0);
lean_dec(v_unused_1891_);
v___x_1874_ = v_x_1863_;
v_isShared_1875_ = v_isSharedCheck_1890_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_tail_1872_);
lean_dec(v_x_1863_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1890_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 1, v_x_1864_);
lean_ctor_set(v___x_1874_, 0, v_a_1877_);
v___x_1879_ = v___x_1874_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1877_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_x_1864_);
v___x_1879_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
v_x_1863_ = v_tail_1872_;
v_x_1864_ = v___x_1879_;
goto _start;
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_del_object(v___x_1874_);
lean_dec(v_tail_1872_);
lean_dec(v_x_1864_);
v_a_1882_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1876_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1876_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v_x_1892_, v_x_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1899_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1900_; double v___x_1901_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = lean_float_of_nat(v___x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object* v_cls_1905_, lean_object* v_msg_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_ref_1912_; lean_object* v___x_1913_; lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1958_; 
v_ref_1912_ = lean_ctor_get(v___y_1909_, 5);
v___x_1913_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1958_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1958_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v_traceState_1919_; lean_object* v_env_1920_; lean_object* v_nextMacroScope_1921_; lean_object* v_ngen_1922_; lean_object* v_auxDeclNGen_1923_; lean_object* v_cache_1924_; lean_object* v_messages_1925_; lean_object* v_infoState_1926_; lean_object* v_snapshotTasks_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1957_; 
v___x_1918_ = lean_st_ref_take(v___y_1910_);
v_traceState_1919_ = lean_ctor_get(v___x_1918_, 4);
v_env_1920_ = lean_ctor_get(v___x_1918_, 0);
v_nextMacroScope_1921_ = lean_ctor_get(v___x_1918_, 1);
v_ngen_1922_ = lean_ctor_get(v___x_1918_, 2);
v_auxDeclNGen_1923_ = lean_ctor_get(v___x_1918_, 3);
v_cache_1924_ = lean_ctor_get(v___x_1918_, 5);
v_messages_1925_ = lean_ctor_get(v___x_1918_, 6);
v_infoState_1926_ = lean_ctor_get(v___x_1918_, 7);
v_snapshotTasks_1927_ = lean_ctor_get(v___x_1918_, 8);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1929_ = v___x_1918_;
v_isShared_1930_ = v_isSharedCheck_1957_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_snapshotTasks_1927_);
lean_inc(v_infoState_1926_);
lean_inc(v_messages_1925_);
lean_inc(v_cache_1924_);
lean_inc(v_traceState_1919_);
lean_inc(v_auxDeclNGen_1923_);
lean_inc(v_ngen_1922_);
lean_inc(v_nextMacroScope_1921_);
lean_inc(v_env_1920_);
lean_dec(v___x_1918_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1957_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
uint64_t v_tid_1931_; lean_object* v_traces_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1956_; 
v_tid_1931_ = lean_ctor_get_uint64(v_traceState_1919_, sizeof(void*)*1);
v_traces_1932_ = lean_ctor_get(v_traceState_1919_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_traceState_1919_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1934_ = v_traceState_1919_;
v_isShared_1935_ = v_isSharedCheck_1956_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_traces_1932_);
lean_dec(v_traceState_1919_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1956_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; double v___x_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
v___x_1938_ = 0;
v___x_1939_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_1940_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1940_, 0, v_cls_1905_);
lean_ctor_set(v___x_1940_, 1, v___x_1936_);
lean_ctor_set(v___x_1940_, 2, v___x_1939_);
lean_ctor_set_float(v___x_1940_, sizeof(void*)*3, v___x_1937_);
lean_ctor_set_float(v___x_1940_, sizeof(void*)*3 + 8, v___x_1937_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*3 + 16, v___x_1938_);
v___x_1941_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2));
v___x_1942_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v_a_1914_);
lean_ctor_set(v___x_1942_, 2, v___x_1941_);
lean_inc(v_ref_1912_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v_ref_1912_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = l_Lean_PersistentArray_push___redArg(v_traces_1932_, v___x_1943_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1944_);
v___x_1946_ = v___x_1934_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1944_);
lean_ctor_set_uint64(v_reuseFailAlloc_1955_, sizeof(void*)*1, v_tid_1931_);
v___x_1946_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1948_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 4, v___x_1946_);
v___x_1948_ = v___x_1929_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_env_1920_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_nextMacroScope_1921_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_ngen_1922_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_auxDeclNGen_1923_);
lean_ctor_set(v_reuseFailAlloc_1954_, 4, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1954_, 5, v_cache_1924_);
lean_ctor_set(v_reuseFailAlloc_1954_, 6, v_messages_1925_);
lean_ctor_set(v_reuseFailAlloc_1954_, 7, v_infoState_1926_);
lean_ctor_set(v_reuseFailAlloc_1954_, 8, v_snapshotTasks_1927_);
v___x_1948_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1949_ = lean_st_ref_set(v___y_1910_, v___x_1948_);
v___x_1950_ = lean_box(0);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1950_);
v___x_1952_ = v___x_1916_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object* v_cls_1959_, lean_object* v_msg_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_1959_, v_msg_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object* v_as_1970_, size_t v_sz_1971_, size_t v_i_1972_, lean_object* v_b_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_a_1980_; uint8_t v___x_1984_; 
v___x_1984_ = lean_usize_dec_lt(v_i_1972_, v_sz_1971_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v_b_1973_);
return v___x_1985_;
}
else
{
lean_object* v_snd_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2076_; 
v_snd_1986_ = lean_ctor_get(v_b_1973_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_b_1973_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v_b_1973_, 0);
lean_dec(v_unused_2077_);
v___x_1988_ = v_b_1973_;
v_isShared_1989_ = v_isSharedCheck_2076_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_snd_1986_);
lean_dec(v_b_1973_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2076_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_array_1990_; lean_object* v_start_1991_; lean_object* v_stop_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_array_1990_ = lean_ctor_get(v_snd_1986_, 0);
v_start_1991_ = lean_ctor_get(v_snd_1986_, 1);
v_stop_1992_ = lean_ctor_get(v_snd_1986_, 2);
v___x_1993_ = lean_box(0);
v___x_1994_ = lean_nat_dec_lt(v_start_1991_, v_stop_1992_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1996_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1993_);
v___x_1996_ = v___x_1988_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_snd_1986_);
v___x_1996_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
return v___x_1997_;
}
}
else
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2072_; 
lean_inc(v_stop_1992_);
lean_inc(v_start_1991_);
lean_inc_ref(v_array_1990_);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_snd_1986_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; lean_object* v_unused_2074_; lean_object* v_unused_2075_; 
v_unused_2073_ = lean_ctor_get(v_snd_1986_, 2);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_snd_1986_, 1);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_snd_1986_, 0);
lean_dec(v_unused_2075_);
v___x_2000_ = v_snd_1986_;
v_isShared_2001_ = v_isSharedCheck_2072_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v_snd_1986_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2072_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2002_ = lean_array_fget(v_array_1990_, v_start_1991_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_add(v_start_1991_, v___x_2003_);
lean_dec(v_start_1991_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2004_);
v___x_2006_ = v___x_2000_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_array_1990_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_stop_1992_);
v___x_2006_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
uint8_t v___x_2007_; uint8_t v___x_2008_; uint8_t v___x_2009_; 
v___x_2007_ = 3;
v___x_2008_ = lean_unbox(v___x_2002_);
lean_dec(v___x_2002_);
v___x_2009_ = l_Lean_instBEqBinderInfo_beq(v___x_2008_, v___x_2007_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2011_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v___x_2006_);
lean_ctor_set(v___x_1988_, 0, v___x_1993_);
v___x_2011_ = v___x_1988_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
v_a_1980_ = v___x_2011_;
goto v___jp_1979_;
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_array_uget_borrowed(v_as_1970_, v_i_1972_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
lean_inc(v___y_1975_);
lean_inc_ref(v___y_1974_);
lean_inc(v_a_2013_);
v___x_2014_ = lean_infer_type(v_a_2013_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = l_Lean_Meta_trySynthInstance(v_a_2015_, v___x_1993_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2054_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2054_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2054_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
if (lean_obj_tag(v_a_2017_) == 1)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; 
lean_del_object(v___x_2019_);
v_a_2021_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v_a_2017_, 1);
lean_inc(v_a_2013_);
v___x_2022_ = l_Lean_Meta_isExprDefEq(v_a_2013_, v_a_2021_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2038_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2038_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2038_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_unbox(v_a_2023_);
lean_dec(v_a_2023_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v___x_2006_);
lean_ctor_set(v___x_1988_, 0, v___x_2028_);
v___x_2030_ = v___x_1988_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2006_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2030_);
v___x_2032_ = v___x_2025_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
else
{
lean_object* v___x_2036_; 
lean_del_object(v___x_2025_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v___x_2006_);
lean_ctor_set(v___x_1988_, 0, v___x_1993_);
v___x_2036_ = v___x_1988_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v___x_2006_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
v_a_1980_ = v___x_2036_;
goto v___jp_1979_;
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v___x_2006_);
lean_del_object(v___x_1988_);
v_a_2039_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2022_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2022_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
lean_dec(v_a_2017_);
v___x_2047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v___x_2006_);
lean_ctor_set(v___x_1988_, 0, v___x_2047_);
v___x_2049_ = v___x_1988_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2006_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2049_);
v___x_2051_ = v___x_2019_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v___x_2006_);
lean_del_object(v___x_1988_);
v_a_2055_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2016_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2016_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref(v___x_2006_);
lean_del_object(v___x_1988_);
v_a_2063_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2014_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2014_);
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
}
}
}
}
}
v___jp_1979_:
{
size_t v___x_1981_; size_t v___x_1982_; 
v___x_1981_ = ((size_t)1ULL);
v___x_1982_ = lean_usize_add(v_i_1972_, v___x_1981_);
v_i_1972_ = v___x_1982_;
v_b_1973_ = v_a_1980_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object* v_as_2078_, lean_object* v_sz_2079_, lean_object* v_i_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
size_t v_sz_boxed_2087_; size_t v_i_boxed_2088_; lean_object* v_res_2089_; 
v_sz_boxed_2087_ = lean_unbox_usize(v_sz_2079_);
lean_dec(v_sz_2079_);
v_i_boxed_2088_ = lean_unbox_usize(v_i_2080_);
lean_dec(v_i_2080_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_as_2078_, v_sz_boxed_2087_, v_i_boxed_2088_, v_b_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v_as_2078_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object* v_as_x27_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
if (lean_obj_tag(v_as_x27_2093_) == 0)
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v_b_2094_);
return v___x_2100_;
}
else
{
lean_object* v_head_2101_; lean_object* v_tail_2102_; lean_object* v_lhs_2103_; lean_object* v_rhs_2104_; lean_object* v___x_2105_; 
lean_dec_ref(v_b_2094_);
v_head_2101_ = lean_ctor_get(v_as_x27_2093_, 0);
v_tail_2102_ = lean_ctor_get(v_as_x27_2093_, 1);
v_lhs_2103_ = lean_ctor_get(v_head_2101_, 0);
v_rhs_2104_ = lean_ctor_get(v_head_2101_, 1);
lean_inc(v___y_2098_);
lean_inc_ref(v___y_2097_);
lean_inc(v___y_2096_);
lean_inc_ref(v___y_2095_);
lean_inc_ref(v_rhs_2104_);
lean_inc_ref(v_lhs_2103_);
v___x_2105_ = lean_is_expr_def_eq(v_lhs_2103_, v_rhs_2104_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2119_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2119_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2119_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = lean_box(0);
v___x_2111_ = lean_unbox(v_a_2106_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_a_2106_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v___x_2110_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2113_);
v___x_2115_ = v___x_2108_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
else
{
lean_object* v___x_2117_; 
lean_del_object(v___x_2108_);
lean_dec(v_a_2106_);
v___x_2117_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_as_x27_2093_ = v_tail_2102_;
v_b_2094_ = v___x_2117_;
goto _start;
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
v_a_2120_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2105_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2105_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object* v_as_x27_2128_, lean_object* v_b_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2128_, v_b_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v_as_x27_2128_);
return v_res_2135_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0);
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
return v___x_2138_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8(void){
_start:
{
lean_object* v_cls_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_cls_2151_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5));
v___x_2152_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__7));
v___x_2153_ = l_Lean_Name_append(v___x_2152_, v_cls_2151_);
return v___x_2153_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__10(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__9));
v___x_2156_ = l_Lean_stringToMessageData(v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object* v_candidate_2157_, lean_object* v_t_2158_, lean_object* v_s_2159_, uint8_t v_mayPostpone_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_Meta_saveState___redArg(v_a_2162_, v_a_2164_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2417_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2417_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2417_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___y_2172_; uint8_t v___y_2173_; lean_object* v_a_2195_; uint8_t v_a_2199_; lean_object* v___x_2211_; lean_object* v_cache_2212_; lean_object* v_mctx_2213_; lean_object* v_zetaDeltaFVarIds_2214_; lean_object* v_postponed_2215_; lean_object* v_diag_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2416_; 
v___x_2211_ = lean_st_ref_take(v_a_2162_);
v_cache_2212_ = lean_ctor_get(v___x_2211_, 1);
v_mctx_2213_ = lean_ctor_get(v___x_2211_, 0);
v_zetaDeltaFVarIds_2214_ = lean_ctor_get(v___x_2211_, 2);
v_postponed_2215_ = lean_ctor_get(v___x_2211_, 3);
v_diag_2216_ = lean_ctor_get(v___x_2211_, 4);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2218_ = v___x_2211_;
v_isShared_2219_ = v_isSharedCheck_2416_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_diag_2216_);
lean_inc(v_postponed_2215_);
lean_inc(v_zetaDeltaFVarIds_2214_);
lean_inc(v_cache_2212_);
lean_inc(v_mctx_2213_);
lean_dec(v___x_2211_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2416_;
goto v_resetjp_2217_;
}
v___jp_2171_:
{
if (v___y_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_del_object(v___x_2169_);
v___x_2174_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2167_, v_a_2162_, v_a_2164_);
lean_dec(v_a_2167_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v___x_2174_, 0);
lean_dec(v_unused_2182_);
v___x_2176_ = v___x_2174_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_dec(v___x_2174_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 1);
lean_ctor_set(v___x_2176_, 0, v___y_2172_);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___y_2172_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref(v___y_2172_);
v_a_2183_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2174_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2174_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v___x_2192_; 
lean_dec(v_a_2167_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set_tag(v___x_2169_, 1);
lean_ctor_set(v___x_2169_, 0, v___y_2172_);
v___x_2192_ = v___x_2169_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___y_2172_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
v___jp_2194_:
{
uint8_t v___x_2196_; 
v___x_2196_ = l_Lean_Exception_isInterrupt(v_a_2195_);
if (v___x_2196_ == 0)
{
uint8_t v___x_2197_; 
lean_inc_ref(v_a_2195_);
v___x_2197_ = l_Lean_Exception_isRuntime(v_a_2195_);
v___y_2172_ = v_a_2195_;
v___y_2173_ = v___x_2197_;
goto v___jp_2171_;
}
else
{
v___y_2172_ = v_a_2195_;
v___y_2173_ = v___x_2196_;
goto v___jp_2171_;
}
}
v___jp_2198_:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2167_, v_a_2162_, v_a_2164_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2208_; 
lean_del_object(v___x_2169_);
lean_dec(v_a_2167_);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v___x_2200_, 0);
lean_dec(v_unused_2209_);
v___x_2202_ = v___x_2200_;
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v___x_2200_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2204_ = lean_box(v_a_2199_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2204_);
v___x_2206_ = v___x_2202_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_object* v_a_2210_; 
v_a_2210_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2200_, 1);
v_a_2195_ = v_a_2210_;
goto v___jp_2194_;
}
}
v_resetjp_2217_:
{
lean_object* v_inferType_2220_; lean_object* v_funInfo_2221_; lean_object* v_synthInstance_2222_; lean_object* v_whnf_2223_; lean_object* v_defEqPerm_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2414_; 
v_inferType_2220_ = lean_ctor_get(v_cache_2212_, 0);
v_funInfo_2221_ = lean_ctor_get(v_cache_2212_, 1);
v_synthInstance_2222_ = lean_ctor_get(v_cache_2212_, 2);
v_whnf_2223_ = lean_ctor_get(v_cache_2212_, 3);
v_defEqPerm_2224_ = lean_ctor_get(v_cache_2212_, 5);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_cache_2212_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v_cache_2212_, 4);
lean_dec(v_unused_2415_);
v___x_2226_ = v_cache_2212_;
v_isShared_2227_ = v_isSharedCheck_2414_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_defEqPerm_2224_);
lean_inc(v_whnf_2223_);
lean_inc(v_synthInstance_2222_);
lean_inc(v_funInfo_2221_);
lean_inc(v_inferType_2220_);
lean_dec(v_cache_2212_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2414_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 4, v___x_2228_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_inferType_2220_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_funInfo_2221_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_synthInstance_2222_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_whnf_2223_);
lean_ctor_set(v_reuseFailAlloc_2413_, 4, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2413_, 5, v_defEqPerm_2224_);
v___x_2230_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2232_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2230_);
v___x_2232_ = v___x_2218_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_mctx_2213_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_zetaDeltaFVarIds_2214_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v_postponed_2215_);
lean_ctor_set(v_reuseFailAlloc_2412_, 4, v_diag_2216_);
v___x_2232_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_st_ref_set(v_a_2162_, v___x_2232_);
v___x_2234_ = l_Lean_Meta_getResetPostponed___redArg(v_a_2162_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; uint8_t v_a_2237_; lean_object* v___x_2278_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
lean_inc(v_candidate_2157_);
v___x_2278_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_candidate_2157_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = l_Lean_ConstantInfo_levelParams(v_a_2279_);
v___x_2281_ = lean_box(0);
v___x_2282_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v___x_2280_, v___x_2281_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = 0;
v___x_2285_ = l_Lean_Core_instantiateValueLevelParams(v_a_2279_, v_a_2283_, v___x_2284_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2279_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = lean_box(0);
v___x_2288_ = l_Lean_Meta_lambdaMetaTelescope(v_a_2286_, v___x_2287_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2286_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v_snd_2290_; lean_object* v_fst_2291_; lean_object* v_fst_2292_; lean_object* v_snd_2293_; lean_object* v___x_2294_; uint8_t v_foApprox_2295_; uint8_t v_ctxApprox_2296_; uint8_t v_quasiPatternApprox_2297_; uint8_t v_constApprox_2298_; uint8_t v_isDefEqStuckEx_2299_; uint8_t v_proofIrrelevance_2300_; uint8_t v_assignSyntheticOpaque_2301_; uint8_t v_offsetCnstrs_2302_; uint8_t v_transparency_2303_; uint8_t v_etaStruct_2304_; uint8_t v_univApprox_2305_; uint8_t v_iota_2306_; uint8_t v_beta_2307_; uint8_t v_proj_2308_; uint8_t v_zeta_2309_; uint8_t v_zetaDelta_2310_; uint8_t v_zetaUnused_2311_; uint8_t v_zetaHave_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2399_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v_snd_2290_ = lean_ctor_get(v_a_2289_, 1);
lean_inc(v_snd_2290_);
v_fst_2291_ = lean_ctor_get(v_a_2289_, 0);
lean_inc(v_fst_2291_);
lean_dec(v_a_2289_);
v_fst_2292_ = lean_ctor_get(v_snd_2290_, 0);
lean_inc(v_fst_2292_);
v_snd_2293_ = lean_ctor_get(v_snd_2290_, 1);
lean_inc(v_snd_2293_);
lean_dec(v_snd_2290_);
v___x_2294_ = l_Lean_Meta_Context_config(v_a_2161_);
v_foApprox_2295_ = lean_ctor_get_uint8(v___x_2294_, 0);
v_ctxApprox_2296_ = lean_ctor_get_uint8(v___x_2294_, 1);
v_quasiPatternApprox_2297_ = lean_ctor_get_uint8(v___x_2294_, 2);
v_constApprox_2298_ = lean_ctor_get_uint8(v___x_2294_, 3);
v_isDefEqStuckEx_2299_ = lean_ctor_get_uint8(v___x_2294_, 4);
v_proofIrrelevance_2300_ = lean_ctor_get_uint8(v___x_2294_, 6);
v_assignSyntheticOpaque_2301_ = lean_ctor_get_uint8(v___x_2294_, 7);
v_offsetCnstrs_2302_ = lean_ctor_get_uint8(v___x_2294_, 8);
v_transparency_2303_ = lean_ctor_get_uint8(v___x_2294_, 9);
v_etaStruct_2304_ = lean_ctor_get_uint8(v___x_2294_, 10);
v_univApprox_2305_ = lean_ctor_get_uint8(v___x_2294_, 11);
v_iota_2306_ = lean_ctor_get_uint8(v___x_2294_, 12);
v_beta_2307_ = lean_ctor_get_uint8(v___x_2294_, 13);
v_proj_2308_ = lean_ctor_get_uint8(v___x_2294_, 14);
v_zeta_2309_ = lean_ctor_get_uint8(v___x_2294_, 15);
v_zetaDelta_2310_ = lean_ctor_get_uint8(v___x_2294_, 16);
v_zetaUnused_2311_ = lean_ctor_get_uint8(v___x_2294_, 17);
v_zetaHave_2312_ = lean_ctor_get_uint8(v___x_2294_, 18);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2314_ = v___x_2294_;
v_isShared_2315_ = v_isSharedCheck_2399_;
goto v_resetjp_2313_;
}
else
{
lean_dec(v___x_2294_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2399_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; 
v___x_2316_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_2293_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_dec_ref_known(v___x_2316_, 1);
lean_del_object(v___x_2314_);
lean_dec(v_fst_2292_);
lean_dec(v_fst_2291_);
lean_dec(v_a_2235_);
lean_dec_ref(v_s_2159_);
lean_dec_ref(v_t_2158_);
lean_dec(v_candidate_2157_);
v_a_2199_ = v___x_2284_;
goto v___jp_2198_;
}
else
{
lean_object* v_a_2317_; uint8_t v_trackZetaDelta_2318_; lean_object* v_zetaDeltaSet_2319_; lean_object* v_lctx_2320_; lean_object* v_localInstances_2321_; lean_object* v_defEqCtx_x3f_2322_; lean_object* v_synthPendingDepth_2323_; lean_object* v_canUnfold_x3f_2324_; uint8_t v_univApprox_2325_; uint8_t v_inTypeClassResolution_2326_; uint8_t v_cacheInferType_2327_; lean_object* v_pattern_2328_; lean_object* v_constraints_2329_; uint8_t v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v_lhs_2362_; lean_object* v_rhs_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2398_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v_trackZetaDelta_2318_ = lean_ctor_get_uint8(v_a_2161_, sizeof(void*)*7);
v_zetaDeltaSet_2319_ = lean_ctor_get(v_a_2161_, 1);
v_lctx_2320_ = lean_ctor_get(v_a_2161_, 2);
v_localInstances_2321_ = lean_ctor_get(v_a_2161_, 3);
v_defEqCtx_x3f_2322_ = lean_ctor_get(v_a_2161_, 4);
v_synthPendingDepth_2323_ = lean_ctor_get(v_a_2161_, 5);
v_canUnfold_x3f_2324_ = lean_ctor_get(v_a_2161_, 6);
v_univApprox_2325_ = lean_ctor_get_uint8(v_a_2161_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2326_ = lean_ctor_get_uint8(v_a_2161_, sizeof(void*)*7 + 2);
v_cacheInferType_2327_ = lean_ctor_get_uint8(v_a_2161_, sizeof(void*)*7 + 3);
v_pattern_2328_ = lean_ctor_get(v_a_2317_, 0);
lean_inc_ref(v_pattern_2328_);
v_constraints_2329_ = lean_ctor_get(v_a_2317_, 1);
lean_inc(v_constraints_2329_);
lean_dec(v_a_2317_);
v_lhs_2362_ = lean_ctor_get(v_pattern_2328_, 0);
v_rhs_2363_ = lean_ctor_get(v_pattern_2328_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_pattern_2328_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2365_ = v_pattern_2328_;
v_isShared_2366_ = v_isSharedCheck_2398_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_rhs_2363_);
lean_inc(v_lhs_2362_);
lean_dec(v_pattern_2328_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2398_;
goto v_resetjp_2364_;
}
v___jp_2330_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2));
v___x_2337_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_constraints_2329_, v___x_2336_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v_constraints_2329_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v_fst_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2359_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v_fst_2339_ = lean_ctor_get(v_a_2338_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_a_2338_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v_a_2338_, 1);
lean_dec(v_unused_2360_);
v___x_2341_ = v_a_2338_;
v_isShared_2342_ = v_isSharedCheck_2359_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_fst_2339_);
lean_dec(v_a_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2359_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
if (lean_obj_tag(v_fst_2339_) == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2343_ = lean_unsigned_to_nat(0u);
v___x_2344_ = lean_array_get_size(v_fst_2292_);
v___x_2345_ = l_Array_toSubarray___redArg(v_fst_2292_, v___x_2343_, v___x_2344_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v___x_2345_);
lean_ctor_set(v___x_2341_, 0, v___x_2287_);
v___x_2347_ = v___x_2341_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
size_t v_sz_2348_; size_t v___x_2349_; lean_object* v___x_2350_; 
v_sz_2348_ = lean_array_size(v_fst_2291_);
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_fst_2291_, v_sz_2348_, v___x_2349_, v___x_2347_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v_fst_2291_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v_fst_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v_fst_2352_ = lean_ctor_get(v_a_2351_, 0);
lean_inc(v_fst_2352_);
lean_dec(v_a_2351_);
if (lean_obj_tag(v_fst_2352_) == 0)
{
v_a_2237_ = v___y_2331_;
goto v___jp_2236_;
}
else
{
lean_object* v_val_2353_; uint8_t v___x_2354_; 
v_val_2353_ = lean_ctor_get(v_fst_2352_, 0);
lean_inc(v_val_2353_);
lean_dec_ref_known(v_fst_2352_, 1);
v___x_2354_ = lean_unbox(v_val_2353_);
lean_dec(v_val_2353_);
v_a_2237_ = v___x_2354_;
goto v___jp_2236_;
}
}
else
{
lean_object* v_a_2355_; 
lean_dec(v_a_2235_);
v_a_2355_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2350_, 1);
v_a_2195_ = v_a_2355_;
goto v___jp_2194_;
}
}
}
else
{
lean_object* v_val_2357_; uint8_t v___x_2358_; 
lean_del_object(v___x_2341_);
lean_dec(v_fst_2292_);
lean_dec(v_fst_2291_);
v_val_2357_ = lean_ctor_get(v_fst_2339_, 0);
lean_inc(v_val_2357_);
lean_dec_ref_known(v_fst_2339_, 1);
v___x_2358_ = lean_unbox(v_val_2357_);
lean_dec(v_val_2357_);
v_a_2237_ = v___x_2358_;
goto v___jp_2236_;
}
}
}
else
{
lean_object* v_a_2361_; 
lean_dec(v_fst_2292_);
lean_dec(v_fst_2291_);
lean_dec(v_a_2235_);
v_a_2361_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2337_, 1);
v_a_2195_ = v_a_2361_;
goto v___jp_2194_;
}
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2315_ == 0)
{
v___x_2368_ = v___x_2314_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 0, v_foApprox_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 1, v_ctxApprox_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 2, v_quasiPatternApprox_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 3, v_constApprox_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 4, v_isDefEqStuckEx_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 6, v_proofIrrelevance_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 7, v_assignSyntheticOpaque_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 8, v_offsetCnstrs_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 9, v_transparency_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 10, v_etaStruct_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 11, v_univApprox_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 12, v_iota_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 13, v_beta_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 14, v_proj_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 15, v_zeta_2309_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 16, v_zetaDelta_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 17, v_zetaUnused_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, 18, v_zetaHave_2312_);
v___x_2368_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
uint64_t v___x_2369_; lean_object* v_cls_2370_; lean_object* v___y_2372_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
lean_ctor_set_uint8(v___x_2368_, 5, v___x_2284_);
v___x_2369_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2368_);
v_cls_2370_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5));
v___x_2391_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2391_, 0, v___x_2368_);
lean_ctor_set_uint64(v___x_2391_, sizeof(void*)*1, v___x_2369_);
lean_inc(v_canUnfold_x3f_2324_);
lean_inc(v_synthPendingDepth_2323_);
lean_inc(v_defEqCtx_x3f_2322_);
lean_inc_ref(v_localInstances_2321_);
lean_inc_ref(v_lctx_2320_);
lean_inc(v_zetaDeltaSet_2319_);
v___x_2392_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
lean_ctor_set(v___x_2392_, 1, v_zetaDeltaSet_2319_);
lean_ctor_set(v___x_2392_, 2, v_lctx_2320_);
lean_ctor_set(v___x_2392_, 3, v_localInstances_2321_);
lean_ctor_set(v___x_2392_, 4, v_defEqCtx_x3f_2322_);
lean_ctor_set(v___x_2392_, 5, v_synthPendingDepth_2323_);
lean_ctor_set(v___x_2392_, 6, v_canUnfold_x3f_2324_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*7, v_trackZetaDelta_2318_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*7 + 1, v_univApprox_2325_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2326_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*7 + 3, v_cacheInferType_2327_);
v___x_2393_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_lhs_2362_, v_t_2158_, v___x_2392_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; uint8_t v___x_2395_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
v___x_2395_ = lean_unbox(v_a_2394_);
lean_dec(v_a_2394_);
if (v___x_2395_ == 0)
{
lean_dec_ref_known(v___x_2392_, 7);
lean_dec_ref(v_rhs_2363_);
lean_dec_ref(v_s_2159_);
v___y_2372_ = v___x_2393_;
goto v___jp_2371_;
}
else
{
lean_object* v___x_2396_; 
lean_dec_ref_known(v___x_2393_, 1);
v___x_2396_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_rhs_2363_, v_s_2159_, v___x_2392_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec_ref_known(v___x_2392_, 7);
v___y_2372_ = v___x_2396_;
goto v___jp_2371_;
}
}
else
{
lean_dec_ref_known(v___x_2392_, 7);
lean_dec_ref(v_rhs_2363_);
lean_dec_ref(v_s_2159_);
v___y_2372_ = v___x_2393_;
goto v___jp_2371_;
}
v___jp_2371_:
{
if (lean_obj_tag(v___y_2372_) == 0)
{
lean_object* v_a_2373_; uint8_t v___x_2374_; 
v_a_2373_ = lean_ctor_get(v___y_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___y_2372_, 1);
v___x_2374_ = lean_unbox(v_a_2373_);
if (v___x_2374_ == 0)
{
lean_dec(v_a_2373_);
lean_del_object(v___x_2365_);
lean_dec(v_constraints_2329_);
lean_dec(v_fst_2292_);
lean_dec(v_fst_2291_);
lean_dec(v_a_2235_);
lean_dec(v_candidate_2157_);
v_a_2199_ = v___x_2284_;
goto v___jp_2198_;
}
else
{
lean_object* v_options_2375_; uint8_t v_hasTrace_2376_; 
v_options_2375_ = lean_ctor_get(v_a_2163_, 2);
v_hasTrace_2376_ = lean_ctor_get_uint8(v_options_2375_, sizeof(void*)*1);
if (v_hasTrace_2376_ == 0)
{
uint8_t v___x_2377_; 
lean_del_object(v___x_2365_);
lean_dec(v_candidate_2157_);
v___x_2377_ = lean_unbox(v_a_2373_);
lean_dec(v_a_2373_);
v___y_2331_ = v___x_2377_;
v___y_2332_ = v_a_2161_;
v___y_2333_ = v_a_2162_;
v___y_2334_ = v_a_2163_;
v___y_2335_ = v_a_2164_;
goto v___jp_2330_;
}
else
{
lean_object* v_inheritedTraceOptions_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_inheritedTraceOptions_2378_ = lean_ctor_get(v_a_2163_, 13);
v___x_2379_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8);
v___x_2380_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2378_, v_options_2375_, v___x_2379_);
if (v___x_2380_ == 0)
{
uint8_t v___x_2381_; 
lean_del_object(v___x_2365_);
lean_dec(v_candidate_2157_);
v___x_2381_ = lean_unbox(v_a_2373_);
lean_dec(v_a_2373_);
v___y_2331_ = v___x_2381_;
v___y_2332_ = v_a_2161_;
v___y_2333_ = v_a_2162_;
v___y_2334_ = v_a_2163_;
v___y_2335_ = v_a_2164_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2382_ = l_Lean_MessageData_ofName(v_candidate_2157_);
v___x_2383_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__10, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__10_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__10);
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 7);
lean_ctor_set(v___x_2365_, 1, v___x_2383_);
lean_ctor_set(v___x_2365_, 0, v___x_2382_);
v___x_2385_ = v___x_2365_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2370_, v___x_2385_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2386_) == 0)
{
uint8_t v___x_2387_; 
lean_dec_ref_known(v___x_2386_, 1);
v___x_2387_ = lean_unbox(v_a_2373_);
lean_dec(v_a_2373_);
v___y_2331_ = v___x_2387_;
v___y_2332_ = v_a_2161_;
v___y_2333_ = v_a_2162_;
v___y_2334_ = v_a_2163_;
v___y_2335_ = v_a_2164_;
goto v___jp_2330_;
}
else
{
lean_object* v_a_2388_; 
lean_dec(v_a_2373_);
lean_dec(v_constraints_2329_);
lean_dec(v_fst_2292_);
lean_dec(v_fst_2291_);
lean_dec(v_a_2235_);
v_a_2388_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2386_, 1);
v_a_2195_ = v_a_2388_;
goto v___jp_2194_;
}
}
}
}
}
}
else
{
lean_object* v_a_2390_; 
lean_del_object(v___x_2365_);
lean_dec(v_constraints_2329_);
lean_dec(v_fst_2292_);
lean_dec(v_fst_2291_);
lean_dec(v_a_2235_);
lean_dec(v_candidate_2157_);
v_a_2390_ = lean_ctor_get(v___y_2372_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___y_2372_, 1);
v_a_2195_ = v_a_2390_;
goto v___jp_2194_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2400_; 
lean_dec(v_a_2235_);
lean_dec_ref(v_s_2159_);
lean_dec_ref(v_t_2158_);
lean_dec(v_candidate_2157_);
v_a_2400_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2288_, 1);
v_a_2195_ = v_a_2400_;
goto v___jp_2194_;
}
}
else
{
lean_object* v_a_2401_; 
lean_dec(v_a_2235_);
lean_dec_ref(v_s_2159_);
lean_dec_ref(v_t_2158_);
lean_dec(v_candidate_2157_);
v_a_2401_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2285_, 1);
v_a_2195_ = v_a_2401_;
goto v___jp_2194_;
}
}
else
{
lean_object* v_a_2402_; 
lean_dec(v_a_2279_);
lean_dec(v_a_2235_);
lean_dec_ref(v_s_2159_);
lean_dec_ref(v_t_2158_);
lean_dec(v_candidate_2157_);
v_a_2402_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2282_, 1);
v_a_2195_ = v_a_2402_;
goto v___jp_2194_;
}
}
else
{
lean_object* v_a_2403_; 
lean_dec(v_a_2235_);
lean_dec_ref(v_s_2159_);
lean_dec_ref(v_t_2158_);
lean_dec(v_candidate_2157_);
v_a_2403_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2278_, 1);
v_a_2195_ = v_a_2403_;
goto v___jp_2194_;
}
v___jp_2236_:
{
if (v_a_2237_ == 0)
{
lean_dec(v_a_2235_);
v_a_2199_ = v_a_2237_;
goto v___jp_2198_;
}
else
{
uint8_t v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = 0;
v___x_2239_ = l_Lean_Meta_processPostponed(v_mayPostpone_2160_, v___x_2238_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2276_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2276_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2276_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_unbox(v_a_2240_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
lean_del_object(v___x_2242_);
lean_dec(v_a_2240_);
lean_dec(v_a_2235_);
v___x_2245_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2167_, v_a_2162_, v_a_2164_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2253_; 
lean_del_object(v___x_2169_);
lean_dec(v_a_2167_);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v___x_2245_, 0);
lean_dec(v_unused_2254_);
v___x_2247_ = v___x_2245_;
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
else
{
lean_dec(v___x_2245_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_box(v___x_2238_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2249_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
else
{
lean_object* v_a_2255_; 
v_a_2255_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2245_, 1);
v_a_2195_ = v_a_2255_;
goto v___jp_2194_;
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_postponed_2258_; lean_object* v_mctx_2259_; lean_object* v_cache_2260_; lean_object* v_zetaDeltaFVarIds_2261_; lean_object* v_diag_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2274_; 
lean_del_object(v___x_2169_);
lean_dec(v_a_2167_);
v___x_2256_ = lean_st_ref_get(v_a_2162_);
v___x_2257_ = lean_st_ref_take(v_a_2162_);
v_postponed_2258_ = lean_ctor_get(v___x_2256_, 3);
lean_inc_ref(v_postponed_2258_);
lean_dec(v___x_2256_);
v_mctx_2259_ = lean_ctor_get(v___x_2257_, 0);
v_cache_2260_ = lean_ctor_get(v___x_2257_, 1);
v_zetaDeltaFVarIds_2261_ = lean_ctor_get(v___x_2257_, 2);
v_diag_2262_ = lean_ctor_get(v___x_2257_, 4);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2274_ == 0)
{
lean_object* v_unused_2275_; 
v_unused_2275_ = lean_ctor_get(v___x_2257_, 3);
lean_dec(v_unused_2275_);
v___x_2264_ = v___x_2257_;
v_isShared_2265_ = v_isSharedCheck_2274_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_diag_2262_);
lean_inc(v_zetaDeltaFVarIds_2261_);
lean_inc(v_cache_2260_);
lean_inc(v_mctx_2259_);
lean_dec(v___x_2257_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2274_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = l_Lean_PersistentArray_append___redArg(v_a_2235_, v_postponed_2258_);
lean_dec_ref(v_postponed_2258_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 3, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_mctx_2259_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_cache_2260_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_zetaDeltaFVarIds_2261_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2273_, 4, v_diag_2262_);
v___x_2268_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = lean_st_ref_set(v_a_2162_, v___x_2268_);
if (v_isShared_2243_ == 0)
{
v___x_2271_ = v___x_2242_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2240_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
}
else
{
lean_object* v_a_2277_; 
lean_dec(v_a_2235_);
v_a_2277_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2239_, 1);
v_a_2195_ = v_a_2277_;
goto v___jp_2194_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_del_object(v___x_2169_);
lean_dec(v_a_2167_);
lean_dec_ref(v_s_2159_);
lean_dec_ref(v_t_2158_);
lean_dec(v_candidate_2157_);
v_a_2404_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2234_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2234_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
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
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec_ref(v_s_2159_);
lean_dec_ref(v_t_2158_);
lean_dec(v_candidate_2157_);
v_a_2418_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2166_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2166_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object* v_candidate_2426_, lean_object* v_t_2427_, lean_object* v_s_2428_, lean_object* v_mayPostpone_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
uint8_t v_mayPostpone_boxed_2435_; lean_object* v_res_2436_; 
v_mayPostpone_boxed_2435_ = lean_unbox(v_mayPostpone_2429_);
v_res_2436_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_candidate_2426_, v_t_2427_, v_s_2428_, v_mayPostpone_boxed_2435_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2436_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0));
v___x_2439_ = l_Lean_stringToMessageData(v___x_2438_);
return v___x_2439_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2));
v___x_2442_ = l_Lean_stringToMessageData(v___x_2441_);
return v___x_2442_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4));
v___x_2445_ = l_Lean_stringToMessageData(v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object* v_candidate_2446_, lean_object* v_t_2447_, lean_object* v_s_2448_, lean_object* v_x_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2455_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1);
v___x_2456_ = l_Lean_MessageData_ofName(v_candidate_2446_);
v___x_2457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = l_Lean_MessageData_ofExpr(v_t_2447_);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = l_Lean_MessageData_ofExpr(v_s_2448_);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object* v_candidate_2467_, lean_object* v_t_2468_, lean_object* v_s_2469_, lean_object* v_x_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(v_candidate_2467_, v_t_2468_, v_s_2469_, v_x_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec_ref(v_x_2470_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__9(lean_object* v_opts_2477_, lean_object* v_opt_2478_){
_start:
{
lean_object* v_name_2479_; lean_object* v_defValue_2480_; lean_object* v_map_2481_; lean_object* v___x_2482_; 
v_name_2479_ = lean_ctor_get(v_opt_2478_, 0);
v_defValue_2480_ = lean_ctor_get(v_opt_2478_, 1);
v_map_2481_ = lean_ctor_get(v_opts_2477_, 0);
v___x_2482_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2481_, v_name_2479_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_inc(v_defValue_2480_);
return v_defValue_2480_;
}
else
{
lean_object* v_val_2483_; 
v_val_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_val_2483_);
lean_dec_ref_known(v___x_2482_, 1);
if (lean_obj_tag(v_val_2483_) == 3)
{
lean_object* v_v_2484_; 
v_v_2484_ = lean_ctor_get(v_val_2483_, 0);
lean_inc(v_v_2484_);
lean_dec_ref_known(v_val_2483_, 1);
return v_v_2484_;
}
else
{
lean_dec(v_val_2483_);
lean_inc(v_defValue_2480_);
return v_defValue_2480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__9___boxed(lean_object* v_opts_2485_, lean_object* v_opt_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__9(v_opts_2485_, v_opt_2486_);
lean_dec_ref(v_opt_2486_);
lean_dec_ref(v_opts_2485_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___redArg(lean_object* v_x_2488_){
_start:
{
if (lean_obj_tag(v_x_2488_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_a_2490_ = lean_ctor_get(v_x_2488_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_x_2488_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v_x_2488_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v_x_2488_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set_tag(v___x_2492_, 1);
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v_a_2498_ = lean_ctor_get(v_x_2488_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_x_2488_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v_x_2488_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v_x_2488_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 0);
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___redArg___boxed(lean_object* v_x_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___redArg(v_x_2506_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6_spec__8(size_t v_sz_2509_, size_t v_i_2510_, lean_object* v_bs_2511_){
_start:
{
uint8_t v___x_2512_; 
v___x_2512_ = lean_usize_dec_lt(v_i_2510_, v_sz_2509_);
if (v___x_2512_ == 0)
{
return v_bs_2511_;
}
else
{
lean_object* v_v_2513_; lean_object* v_msg_2514_; lean_object* v___x_2515_; lean_object* v_bs_x27_2516_; size_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
v_v_2513_ = lean_array_uget_borrowed(v_bs_2511_, v_i_2510_);
v_msg_2514_ = lean_ctor_get(v_v_2513_, 1);
lean_inc_ref(v_msg_2514_);
v___x_2515_ = lean_unsigned_to_nat(0u);
v_bs_x27_2516_ = lean_array_uset(v_bs_2511_, v_i_2510_, v___x_2515_);
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_add(v_i_2510_, v___x_2517_);
v___x_2519_ = lean_array_uset(v_bs_x27_2516_, v_i_2510_, v_msg_2514_);
v_i_2510_ = v___x_2518_;
v_bs_2511_ = v___x_2519_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6_spec__8___boxed(lean_object* v_sz_2521_, lean_object* v_i_2522_, lean_object* v_bs_2523_){
_start:
{
size_t v_sz_boxed_2524_; size_t v_i_boxed_2525_; lean_object* v_res_2526_; 
v_sz_boxed_2524_ = lean_unbox_usize(v_sz_2521_);
lean_dec(v_sz_2521_);
v_i_boxed_2525_ = lean_unbox_usize(v_i_2522_);
lean_dec(v_i_2522_);
v_res_2526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6_spec__8(v_sz_boxed_2524_, v_i_boxed_2525_, v_bs_2523_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6(lean_object* v_oldTraces_2527_, lean_object* v_data_2528_, lean_object* v_ref_2529_, lean_object* v_msg_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_fileName_2536_; lean_object* v_fileMap_2537_; lean_object* v_options_2538_; lean_object* v_currRecDepth_2539_; lean_object* v_maxRecDepth_2540_; lean_object* v_ref_2541_; lean_object* v_currNamespace_2542_; lean_object* v_openDecls_2543_; lean_object* v_initHeartbeats_2544_; lean_object* v_maxHeartbeats_2545_; lean_object* v_quotContext_2546_; lean_object* v_currMacroScope_2547_; uint8_t v_diag_2548_; lean_object* v_cancelTk_x3f_2549_; uint8_t v_suppressElabErrors_2550_; lean_object* v_inheritedTraceOptions_2551_; lean_object* v___x_2552_; lean_object* v_traceState_2553_; lean_object* v_traces_2554_; lean_object* v_ref_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; size_t v_sz_2558_; size_t v___x_2559_; lean_object* v___x_2560_; lean_object* v_msg_2561_; lean_object* v___x_2562_; lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2600_; 
v_fileName_2536_ = lean_ctor_get(v___y_2533_, 0);
v_fileMap_2537_ = lean_ctor_get(v___y_2533_, 1);
v_options_2538_ = lean_ctor_get(v___y_2533_, 2);
v_currRecDepth_2539_ = lean_ctor_get(v___y_2533_, 3);
v_maxRecDepth_2540_ = lean_ctor_get(v___y_2533_, 4);
v_ref_2541_ = lean_ctor_get(v___y_2533_, 5);
v_currNamespace_2542_ = lean_ctor_get(v___y_2533_, 6);
v_openDecls_2543_ = lean_ctor_get(v___y_2533_, 7);
v_initHeartbeats_2544_ = lean_ctor_get(v___y_2533_, 8);
v_maxHeartbeats_2545_ = lean_ctor_get(v___y_2533_, 9);
v_quotContext_2546_ = lean_ctor_get(v___y_2533_, 10);
v_currMacroScope_2547_ = lean_ctor_get(v___y_2533_, 11);
v_diag_2548_ = lean_ctor_get_uint8(v___y_2533_, sizeof(void*)*14);
v_cancelTk_x3f_2549_ = lean_ctor_get(v___y_2533_, 12);
v_suppressElabErrors_2550_ = lean_ctor_get_uint8(v___y_2533_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2551_ = lean_ctor_get(v___y_2533_, 13);
v___x_2552_ = lean_st_ref_get(v___y_2534_);
v_traceState_2553_ = lean_ctor_get(v___x_2552_, 4);
lean_inc_ref(v_traceState_2553_);
lean_dec(v___x_2552_);
v_traces_2554_ = lean_ctor_get(v_traceState_2553_, 0);
lean_inc_ref(v_traces_2554_);
lean_dec_ref(v_traceState_2553_);
v_ref_2555_ = l_Lean_replaceRef(v_ref_2529_, v_ref_2541_);
lean_inc_ref(v_inheritedTraceOptions_2551_);
lean_inc(v_cancelTk_x3f_2549_);
lean_inc(v_currMacroScope_2547_);
lean_inc(v_quotContext_2546_);
lean_inc(v_maxHeartbeats_2545_);
lean_inc(v_initHeartbeats_2544_);
lean_inc(v_openDecls_2543_);
lean_inc(v_currNamespace_2542_);
lean_inc(v_maxRecDepth_2540_);
lean_inc(v_currRecDepth_2539_);
lean_inc_ref(v_options_2538_);
lean_inc_ref(v_fileMap_2537_);
lean_inc_ref(v_fileName_2536_);
v___x_2556_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2556_, 0, v_fileName_2536_);
lean_ctor_set(v___x_2556_, 1, v_fileMap_2537_);
lean_ctor_set(v___x_2556_, 2, v_options_2538_);
lean_ctor_set(v___x_2556_, 3, v_currRecDepth_2539_);
lean_ctor_set(v___x_2556_, 4, v_maxRecDepth_2540_);
lean_ctor_set(v___x_2556_, 5, v_ref_2555_);
lean_ctor_set(v___x_2556_, 6, v_currNamespace_2542_);
lean_ctor_set(v___x_2556_, 7, v_openDecls_2543_);
lean_ctor_set(v___x_2556_, 8, v_initHeartbeats_2544_);
lean_ctor_set(v___x_2556_, 9, v_maxHeartbeats_2545_);
lean_ctor_set(v___x_2556_, 10, v_quotContext_2546_);
lean_ctor_set(v___x_2556_, 11, v_currMacroScope_2547_);
lean_ctor_set(v___x_2556_, 12, v_cancelTk_x3f_2549_);
lean_ctor_set(v___x_2556_, 13, v_inheritedTraceOptions_2551_);
lean_ctor_set_uint8(v___x_2556_, sizeof(void*)*14, v_diag_2548_);
lean_ctor_set_uint8(v___x_2556_, sizeof(void*)*14 + 1, v_suppressElabErrors_2550_);
v___x_2557_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2554_);
lean_dec_ref(v_traces_2554_);
v_sz_2558_ = lean_array_size(v___x_2557_);
v___x_2559_ = ((size_t)0ULL);
v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6_spec__8(v_sz_2558_, v___x_2559_, v___x_2557_);
v_msg_2561_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2561_, 0, v_data_2528_);
lean_ctor_set(v_msg_2561_, 1, v_msg_2530_);
lean_ctor_set(v_msg_2561_, 2, v___x_2560_);
v___x_2562_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2561_, v___y_2531_, v___y_2532_, v___x_2556_, v___y_2534_);
lean_dec_ref_known(v___x_2556_, 14);
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2600_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2600_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v_traceState_2568_; lean_object* v_env_2569_; lean_object* v_nextMacroScope_2570_; lean_object* v_ngen_2571_; lean_object* v_auxDeclNGen_2572_; lean_object* v_cache_2573_; lean_object* v_messages_2574_; lean_object* v_infoState_2575_; lean_object* v_snapshotTasks_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2599_; 
v___x_2567_ = lean_st_ref_take(v___y_2534_);
v_traceState_2568_ = lean_ctor_get(v___x_2567_, 4);
v_env_2569_ = lean_ctor_get(v___x_2567_, 0);
v_nextMacroScope_2570_ = lean_ctor_get(v___x_2567_, 1);
v_ngen_2571_ = lean_ctor_get(v___x_2567_, 2);
v_auxDeclNGen_2572_ = lean_ctor_get(v___x_2567_, 3);
v_cache_2573_ = lean_ctor_get(v___x_2567_, 5);
v_messages_2574_ = lean_ctor_get(v___x_2567_, 6);
v_infoState_2575_ = lean_ctor_get(v___x_2567_, 7);
v_snapshotTasks_2576_ = lean_ctor_get(v___x_2567_, 8);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2578_ = v___x_2567_;
v_isShared_2579_ = v_isSharedCheck_2599_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_snapshotTasks_2576_);
lean_inc(v_infoState_2575_);
lean_inc(v_messages_2574_);
lean_inc(v_cache_2573_);
lean_inc(v_traceState_2568_);
lean_inc(v_auxDeclNGen_2572_);
lean_inc(v_ngen_2571_);
lean_inc(v_nextMacroScope_2570_);
lean_inc(v_env_2569_);
lean_dec(v___x_2567_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2599_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
uint64_t v_tid_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2597_; 
v_tid_2580_ = lean_ctor_get_uint64(v_traceState_2568_, sizeof(void*)*1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_traceState_2568_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v_traceState_2568_, 0);
lean_dec(v_unused_2598_);
v___x_2582_ = v_traceState_2568_;
v_isShared_2583_ = v_isSharedCheck_2597_;
goto v_resetjp_2581_;
}
else
{
lean_dec(v_traceState_2568_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2597_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_ref_2529_);
lean_ctor_set(v___x_2584_, 1, v_a_2563_);
v___x_2585_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2527_, v___x_2584_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2585_);
v___x_2587_ = v___x_2582_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2585_);
lean_ctor_set_uint64(v_reuseFailAlloc_2596_, sizeof(void*)*1, v_tid_2580_);
v___x_2587_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2589_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 4, v___x_2587_);
v___x_2589_ = v___x_2578_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_env_2569_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_nextMacroScope_2570_);
lean_ctor_set(v_reuseFailAlloc_2595_, 2, v_ngen_2571_);
lean_ctor_set(v_reuseFailAlloc_2595_, 3, v_auxDeclNGen_2572_);
lean_ctor_set(v_reuseFailAlloc_2595_, 4, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2595_, 5, v_cache_2573_);
lean_ctor_set(v_reuseFailAlloc_2595_, 6, v_messages_2574_);
lean_ctor_set(v_reuseFailAlloc_2595_, 7, v_infoState_2575_);
lean_ctor_set(v_reuseFailAlloc_2595_, 8, v_snapshotTasks_2576_);
v___x_2589_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2590_ = lean_st_ref_set(v___y_2534_, v___x_2589_);
v___x_2591_ = lean_box(0);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2591_);
v___x_2593_ = v___x_2565_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6___boxed(lean_object* v_oldTraces_2601_, lean_object* v_data_2602_, lean_object* v_ref_2603_, lean_object* v_msg_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6(v_oldTraces_2601_, v_data_2602_, v_ref_2603_, v_msg_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
return v_res_2610_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__8(lean_object* v_e_2611_){
_start:
{
if (lean_obj_tag(v_e_2611_) == 0)
{
uint8_t v___x_2612_; 
v___x_2612_ = 2;
return v___x_2612_;
}
else
{
lean_object* v_a_2613_; uint8_t v___x_2614_; 
v_a_2613_ = lean_ctor_get(v_e_2611_, 0);
v___x_2614_ = lean_unbox(v_a_2613_);
if (v___x_2614_ == 0)
{
uint8_t v___x_2615_; 
v___x_2615_ = 1;
return v___x_2615_;
}
else
{
uint8_t v___x_2616_; 
v___x_2616_ = 0;
return v___x_2616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__8___boxed(lean_object* v_e_2617_){
_start:
{
uint8_t v_res_2618_; lean_object* v_r_2619_; 
v_res_2618_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__8(v_e_2617_);
lean_dec_ref(v_e_2617_);
v_r_2619_ = lean_box(v_res_2618_);
return v_r_2619_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__1(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__0));
v___x_2622_ = l_Lean_stringToMessageData(v___x_2621_);
return v___x_2622_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2623_; double v___x_2624_; 
v___x_2623_ = lean_unsigned_to_nat(1000u);
v___x_2624_ = lean_float_of_nat(v___x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object* v_cls_2625_, uint8_t v_collapsed_2626_, lean_object* v_tag_2627_, lean_object* v_opts_2628_, uint8_t v_clsEnabled_2629_, lean_object* v_oldTraces_2630_, lean_object* v_msg_2631_, lean_object* v_resStartStop_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_fst_2638_; lean_object* v_snd_2639_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v_data_2643_; lean_object* v_fst_2654_; lean_object* v_snd_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___y_2659_; lean_object* v_a_2660_; uint8_t v___y_2675_; double v___y_2706_; 
v_fst_2638_ = lean_ctor_get(v_resStartStop_2632_, 0);
lean_inc(v_fst_2638_);
v_snd_2639_ = lean_ctor_get(v_resStartStop_2632_, 1);
lean_inc(v_snd_2639_);
lean_dec_ref(v_resStartStop_2632_);
v_fst_2654_ = lean_ctor_get(v_snd_2639_, 0);
lean_inc(v_fst_2654_);
v_snd_2655_ = lean_ctor_get(v_snd_2639_, 1);
lean_inc(v_snd_2655_);
lean_dec(v_snd_2639_);
v___x_2656_ = l_Lean_trace_profiler;
v___x_2657_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v_opts_2628_, v___x_2656_);
if (v___x_2657_ == 0)
{
v___y_2675_ = v___x_2657_;
goto v___jp_2674_;
}
else
{
lean_object* v___x_2711_; uint8_t v___x_2712_; 
v___x_2711_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2712_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v_opts_2628_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; double v___x_2715_; double v___x_2716_; double v___x_2717_; 
v___x_2713_ = l_Lean_trace_profiler_threshold;
v___x_2714_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__9(v_opts_2628_, v___x_2713_);
v___x_2715_ = lean_float_of_nat(v___x_2714_);
v___x_2716_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__2);
v___x_2717_ = lean_float_div(v___x_2715_, v___x_2716_);
v___y_2706_ = v___x_2717_;
goto v___jp_2705_;
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; double v___x_2720_; 
v___x_2718_ = l_Lean_trace_profiler_threshold;
v___x_2719_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__9(v_opts_2628_, v___x_2718_);
v___x_2720_ = lean_float_of_nat(v___x_2719_);
v___y_2706_ = v___x_2720_;
goto v___jp_2705_;
}
}
v___jp_2640_:
{
lean_object* v___x_2644_; 
lean_inc(v___y_2642_);
v___x_2644_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__6(v_oldTraces_2630_, v_data_2643_, v___y_2642_, v___y_2641_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; 
lean_dec_ref_known(v___x_2644_, 1);
v___x_2645_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___redArg(v_fst_2638_);
return v___x_2645_;
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_fst_2638_);
v_a_2646_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2644_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2644_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
v___jp_2658_:
{
uint8_t v_result_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; double v___x_2664_; lean_object* v_data_2665_; 
v_result_2661_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__8(v_fst_2638_);
v___x_2662_ = lean_box(v_result_2661_);
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
v___x_2664_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
lean_inc_ref(v_tag_2627_);
lean_inc_ref(v___x_2663_);
lean_inc(v_cls_2625_);
v_data_2665_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2665_, 0, v_cls_2625_);
lean_ctor_set(v_data_2665_, 1, v___x_2663_);
lean_ctor_set(v_data_2665_, 2, v_tag_2627_);
lean_ctor_set_float(v_data_2665_, sizeof(void*)*3, v___x_2664_);
lean_ctor_set_float(v_data_2665_, sizeof(void*)*3 + 8, v___x_2664_);
lean_ctor_set_uint8(v_data_2665_, sizeof(void*)*3 + 16, v_collapsed_2626_);
if (v___x_2657_ == 0)
{
lean_dec_ref_known(v___x_2663_, 1);
lean_dec(v_snd_2655_);
lean_dec(v_fst_2654_);
lean_dec_ref(v_tag_2627_);
lean_dec(v_cls_2625_);
v___y_2641_ = v_a_2660_;
v___y_2642_ = v___y_2659_;
v_data_2643_ = v_data_2665_;
goto v___jp_2640_;
}
else
{
lean_object* v_data_2666_; double v___x_2667_; double v___x_2668_; 
lean_dec_ref_known(v_data_2665_, 3);
v_data_2666_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2666_, 0, v_cls_2625_);
lean_ctor_set(v_data_2666_, 1, v___x_2663_);
lean_ctor_set(v_data_2666_, 2, v_tag_2627_);
v___x_2667_ = lean_unbox_float(v_fst_2654_);
lean_dec(v_fst_2654_);
lean_ctor_set_float(v_data_2666_, sizeof(void*)*3, v___x_2667_);
v___x_2668_ = lean_unbox_float(v_snd_2655_);
lean_dec(v_snd_2655_);
lean_ctor_set_float(v_data_2666_, sizeof(void*)*3 + 8, v___x_2668_);
lean_ctor_set_uint8(v_data_2666_, sizeof(void*)*3 + 16, v_collapsed_2626_);
v___y_2641_ = v_a_2660_;
v___y_2642_ = v___y_2659_;
v_data_2643_ = v_data_2666_;
goto v___jp_2640_;
}
}
v___jp_2669_:
{
lean_object* v_ref_2670_; lean_object* v___x_2671_; 
v_ref_2670_ = lean_ctor_get(v___y_2635_, 5);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
lean_inc(v___y_2634_);
lean_inc_ref(v___y_2633_);
lean_inc(v_fst_2638_);
v___x_2671_ = lean_apply_6(v_msg_2631_, v_fst_2638_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, lean_box(0));
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v___y_2659_ = v_ref_2670_;
v_a_2660_ = v_a_2672_;
goto v___jp_2658_;
}
else
{
lean_object* v___x_2673_; 
lean_dec_ref_known(v___x_2671_, 1);
v___x_2673_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___closed__1);
v___y_2659_ = v_ref_2670_;
v_a_2660_ = v___x_2673_;
goto v___jp_2658_;
}
}
v___jp_2674_:
{
if (v_clsEnabled_2629_ == 0)
{
if (v___y_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v_traceState_2677_; lean_object* v_env_2678_; lean_object* v_nextMacroScope_2679_; lean_object* v_ngen_2680_; lean_object* v_auxDeclNGen_2681_; lean_object* v_cache_2682_; lean_object* v_messages_2683_; lean_object* v_infoState_2684_; lean_object* v_snapshotTasks_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v_snd_2655_);
lean_dec(v_fst_2654_);
lean_dec_ref(v_msg_2631_);
lean_dec_ref(v_tag_2627_);
lean_dec(v_cls_2625_);
v___x_2676_ = lean_st_ref_take(v___y_2636_);
v_traceState_2677_ = lean_ctor_get(v___x_2676_, 4);
v_env_2678_ = lean_ctor_get(v___x_2676_, 0);
v_nextMacroScope_2679_ = lean_ctor_get(v___x_2676_, 1);
v_ngen_2680_ = lean_ctor_get(v___x_2676_, 2);
v_auxDeclNGen_2681_ = lean_ctor_get(v___x_2676_, 3);
v_cache_2682_ = lean_ctor_get(v___x_2676_, 5);
v_messages_2683_ = lean_ctor_get(v___x_2676_, 6);
v_infoState_2684_ = lean_ctor_get(v___x_2676_, 7);
v_snapshotTasks_2685_ = lean_ctor_get(v___x_2676_, 8);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2687_ = v___x_2676_;
v_isShared_2688_ = v_isSharedCheck_2704_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snapshotTasks_2685_);
lean_inc(v_infoState_2684_);
lean_inc(v_messages_2683_);
lean_inc(v_cache_2682_);
lean_inc(v_traceState_2677_);
lean_inc(v_auxDeclNGen_2681_);
lean_inc(v_ngen_2680_);
lean_inc(v_nextMacroScope_2679_);
lean_inc(v_env_2678_);
lean_dec(v___x_2676_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2704_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
uint64_t v_tid_2689_; lean_object* v_traces_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2703_; 
v_tid_2689_ = lean_ctor_get_uint64(v_traceState_2677_, sizeof(void*)*1);
v_traces_2690_ = lean_ctor_get(v_traceState_2677_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_traceState_2677_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2692_ = v_traceState_2677_;
v_isShared_2693_ = v_isSharedCheck_2703_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_traces_2690_);
lean_dec(v_traceState_2677_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2703_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2694_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2630_, v_traces_2690_);
lean_dec_ref(v_traces_2690_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2694_);
v___x_2696_ = v___x_2692_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2694_);
lean_ctor_set_uint64(v_reuseFailAlloc_2702_, sizeof(void*)*1, v_tid_2689_);
v___x_2696_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 4, v___x_2696_);
v___x_2698_ = v___x_2687_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_env_2678_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_nextMacroScope_2679_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_ngen_2680_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_auxDeclNGen_2681_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2701_, 5, v_cache_2682_);
lean_ctor_set(v_reuseFailAlloc_2701_, 6, v_messages_2683_);
lean_ctor_set(v_reuseFailAlloc_2701_, 7, v_infoState_2684_);
lean_ctor_set(v_reuseFailAlloc_2701_, 8, v_snapshotTasks_2685_);
v___x_2698_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_st_ref_set(v___y_2636_, v___x_2698_);
v___x_2700_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___redArg(v_fst_2638_);
return v___x_2700_;
}
}
}
}
}
else
{
goto v___jp_2669_;
}
}
else
{
goto v___jp_2669_;
}
}
v___jp_2705_:
{
double v___x_2707_; double v___x_2708_; double v___x_2709_; uint8_t v___x_2710_; 
v___x_2707_ = lean_unbox_float(v_snd_2655_);
v___x_2708_ = lean_unbox_float(v_fst_2654_);
v___x_2709_ = lean_float_sub(v___x_2707_, v___x_2708_);
v___x_2710_ = lean_float_decLt(v___y_2706_, v___x_2709_);
v___y_2675_ = v___x_2710_;
goto v___jp_2674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object* v_cls_2721_, lean_object* v_collapsed_2722_, lean_object* v_tag_2723_, lean_object* v_opts_2724_, lean_object* v_clsEnabled_2725_, lean_object* v_oldTraces_2726_, lean_object* v_msg_2727_, lean_object* v_resStartStop_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v_collapsed_boxed_2734_; uint8_t v_clsEnabled_boxed_2735_; lean_object* v_res_2736_; 
v_collapsed_boxed_2734_ = lean_unbox(v_collapsed_2722_);
v_clsEnabled_boxed_2735_ = lean_unbox(v_clsEnabled_2725_);
v_res_2736_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_cls_2721_, v_collapsed_boxed_2734_, v_tag_2723_, v_opts_2724_, v_clsEnabled_boxed_2735_, v_oldTraces_2726_, v_msg_2727_, v_resStartStop_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec_ref(v_opts_2724_);
return v_res_2736_;
}
}
static double _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0(void){
_start:
{
lean_object* v___x_2737_; double v___x_2738_; 
v___x_2737_ = lean_unsigned_to_nat(1000000000u);
v___x_2738_ = lean_float_of_nat(v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object* v_t_2739_, lean_object* v_s_2740_, lean_object* v_candidate_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_options_2747_; lean_object* v_inheritedTraceOptions_2748_; uint8_t v_hasTrace_2749_; uint8_t v___x_2750_; uint8_t v___x_2751_; 
v_options_2747_ = lean_ctor_get(v_a_2744_, 2);
v_inheritedTraceOptions_2748_ = lean_ctor_get(v_a_2744_, 13);
v_hasTrace_2749_ = lean_ctor_get_uint8(v_options_2747_, sizeof(void*)*1);
v___x_2750_ = 1;
v___x_2751_ = lean_bool_not(v_hasTrace_2749_);
if (v___x_2751_ == 0)
{
lean_object* v___f_2752_; lean_object* v_cls_2753_; lean_object* v___x_2754_; lean_object* v___y_2756_; uint8_t v___y_2757_; lean_object* v___y_2758_; lean_object* v_a_2759_; lean_object* v___y_2772_; lean_object* v___y_2773_; uint8_t v___y_2774_; lean_object* v_a_2775_; uint8_t v___y_2785_; uint8_t v_a_2827_; 
lean_inc_ref(v_s_2740_);
lean_inc_ref(v_t_2739_);
lean_inc(v_candidate_2741_);
v___f_2752_ = lean_alloc_closure((void*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2752_, 0, v_candidate_2741_);
lean_closure_set(v___f_2752_, 1, v_t_2739_);
lean_closure_set(v___f_2752_, 2, v_s_2740_);
v_cls_2753_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5));
v___x_2754_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
if (v_hasTrace_2749_ == 0)
{
v_a_2827_ = v_hasTrace_2749_;
goto v___jp_2826_;
}
else
{
lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2831_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8);
v___x_2832_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2748_, v_options_2747_, v___x_2831_);
if (v___x_2832_ == 0)
{
v_a_2827_ = v___x_2832_;
goto v___jp_2826_;
}
else
{
v___y_2785_ = v___x_2832_;
goto v___jp_2784_;
}
}
v___jp_2755_:
{
lean_object* v___x_2760_; double v___x_2761_; double v___x_2762_; double v___x_2763_; double v___x_2764_; double v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2760_ = lean_io_mono_nanos_now();
v___x_2761_ = lean_float_of_nat(v___y_2758_);
v___x_2762_ = lean_float_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0);
v___x_2763_ = lean_float_div(v___x_2761_, v___x_2762_);
v___x_2764_ = lean_float_of_nat(v___x_2760_);
v___x_2765_ = lean_float_div(v___x_2764_, v___x_2762_);
v___x_2766_ = lean_box_float(v___x_2763_);
v___x_2767_ = lean_box_float(v___x_2765_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v_a_2759_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_cls_2753_, v___x_2750_, v___x_2754_, v_options_2747_, v___y_2757_, v___y_2756_, v___f_2752_, v___x_2769_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
return v___x_2770_;
}
v___jp_2771_:
{
lean_object* v___x_2776_; double v___x_2777_; double v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2776_ = lean_io_get_num_heartbeats();
v___x_2777_ = lean_float_of_nat(v___y_2773_);
v___x_2778_ = lean_float_of_nat(v___x_2776_);
v___x_2779_ = lean_box_float(v___x_2777_);
v___x_2780_ = lean_box_float(v___x_2778_);
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_a_2775_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_cls_2753_, v___x_2750_, v___x_2754_, v_options_2747_, v___y_2774_, v___y_2772_, v___f_2752_, v___x_2782_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
return v___x_2783_;
}
v___jp_2784_:
{
lean_object* v___x_2786_; lean_object* v_a_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2786_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___redArg(v_a_2745_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2789_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v_options_2747_, v___x_2788_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_io_mono_nanos_now();
v___x_2791_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_candidate_2741_, v_t_2739_, v_s_2740_, v___x_2750_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set_tag(v___x_2794_, 1);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
v___y_2756_ = v_a_2787_;
v___y_2757_ = v___y_2785_;
v___y_2758_ = v___x_2790_;
v_a_2759_ = v___x_2797_;
goto v___jp_2755_;
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_a_2800_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2791_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2791_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set_tag(v___x_2802_, 0);
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
v___y_2756_ = v_a_2787_;
v___y_2757_ = v___y_2785_;
v___y_2758_ = v___x_2790_;
v_a_2759_ = v___x_2805_;
goto v___jp_2755_;
}
}
}
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_io_get_num_heartbeats();
v___x_2809_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_candidate_2741_, v_t_2739_, v_s_2740_, v___x_2750_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set_tag(v___x_2812_, 1);
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
v___y_2772_ = v_a_2787_;
v___y_2773_ = v___x_2808_;
v___y_2774_ = v___y_2785_;
v_a_2775_ = v___x_2815_;
goto v___jp_2771_;
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
v_a_2818_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2809_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2809_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set_tag(v___x_2820_, 0);
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
v___y_2772_ = v_a_2787_;
v___y_2773_ = v___x_2808_;
v___y_2774_ = v___y_2785_;
v_a_2775_ = v___x_2823_;
goto v___jp_2771_;
}
}
}
}
}
v___jp_2826_:
{
lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = l_Lean_trace_profiler;
v___x_2829_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v_options_2747_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; 
lean_dec_ref(v___f_2752_);
v___x_2830_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_candidate_2741_, v_t_2739_, v_s_2740_, v___x_2750_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
return v___x_2830_;
}
else
{
v___y_2785_ = v_a_2827_;
goto v___jp_2784_;
}
}
}
else
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_candidate_2741_, v_t_2739_, v_s_2740_, v___x_2750_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object* v_t_2834_, lean_object* v_s_2835_, lean_object* v_candidate_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2834_, v_s_2835_, v_candidate_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object* v_as_2843_, lean_object* v_as_x27_2844_, lean_object* v_b_2845_, lean_object* v_a_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2844_, v_b_2845_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object* v_as_2853_, lean_object* v_as_x27_2854_, lean_object* v_b_2855_, lean_object* v_a_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(v_as_2853_, v_as_x27_2854_, v_b_2855_, v_a_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v_as_x27_2854_);
lean_dec(v_as_2853_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7(lean_object* v_00_u03b1_2863_, lean_object* v_x_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___redArg(v_x_2864_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7___boxed(lean_object* v_00_u03b1_2871_, lean_object* v_x_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6_spec__7(v_00_u03b1_2871_, v_x_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(lean_object* v_t_2879_, lean_object* v_s_2880_, uint8_t v___x_2881_, lean_object* v_as_2882_, size_t v_sz_2883_, size_t v_i_2884_, lean_object* v_b_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
uint8_t v___x_2891_; 
v___x_2891_ = lean_usize_dec_lt(v_i_2884_, v_sz_2883_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_dec_ref(v_s_2880_);
lean_dec_ref(v_t_2879_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_b_2885_);
return v___x_2892_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2894_; 
lean_dec_ref(v_b_2885_);
v_a_2893_ = lean_array_uget_borrowed(v_as_2882_, v_i_2884_);
lean_inc(v_a_2893_);
lean_inc_ref(v_s_2880_);
lean_inc_ref(v_t_2879_);
v___x_2894_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2879_, v_s_2880_, v_a_2893_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2911_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2911_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2911_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; uint8_t v___x_2900_; 
v___x_2899_ = lean_box(0);
v___x_2900_ = lean_unbox(v_a_2895_);
lean_dec(v_a_2895_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; 
lean_del_object(v___x_2897_);
v___x_2901_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v___x_2902_ = ((size_t)1ULL);
v___x_2903_ = lean_usize_add(v_i_2884_, v___x_2902_);
v_i_2884_ = v___x_2903_;
v_b_2885_ = v___x_2901_;
goto _start;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
lean_dec_ref(v_s_2880_);
lean_dec_ref(v_t_2879_);
v___x_2905_ = lean_box(v___x_2881_);
v___x_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
lean_ctor_set(v___x_2907_, 1, v___x_2899_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2907_);
v___x_2909_ = v___x_2897_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v_s_2880_);
lean_dec_ref(v_t_2879_);
v_a_2912_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2894_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2894_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object* v_t_2920_, lean_object* v_s_2921_, lean_object* v___x_2922_, lean_object* v_as_2923_, lean_object* v_sz_2924_, lean_object* v_i_2925_, lean_object* v_b_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
uint8_t v___x_3586__boxed_2932_; size_t v_sz_boxed_2933_; size_t v_i_boxed_2934_; lean_object* v_res_2935_; 
v___x_3586__boxed_2932_ = lean_unbox(v___x_2922_);
v_sz_boxed_2933_ = lean_unbox_usize(v_sz_2924_);
lean_dec(v_sz_2924_);
v_i_boxed_2934_ = lean_unbox_usize(v_i_2925_);
lean_dec(v_i_2925_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2920_, v_s_2921_, v___x_3586__boxed_2932_, v_as_2923_, v_sz_boxed_2933_, v_i_boxed_2934_, v_b_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v_as_2923_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* v_t_2936_, lean_object* v_s_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v_options_3015_; uint8_t v_hasTrace_3016_; 
v_options_3015_ = lean_ctor_get(v_a_2940_, 2);
v_hasTrace_3016_ = lean_ctor_get_uint8(v_options_3015_, sizeof(void*)*1);
if (v_hasTrace_3016_ == 0)
{
v___y_2944_ = v_a_2938_;
v___y_2945_ = v_a_2939_;
v___y_2946_ = v_a_2940_;
v___y_2947_ = v_a_2941_;
goto v___jp_2943_;
}
else
{
lean_object* v_inheritedTraceOptions_3017_; lean_object* v_cls_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_inheritedTraceOptions_3017_ = lean_ctor_get(v_a_2940_, 13);
v_cls_3018_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5));
v___x_3019_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__8);
v___x_3020_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3017_, v_options_3015_, v___x_3019_);
if (v___x_3020_ == 0)
{
v___y_2944_ = v_a_2938_;
v___y_2945_ = v_a_2939_;
v___y_2946_ = v_a_2940_;
v___y_2947_ = v_a_2941_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_inc_ref(v_t_2936_);
v___x_3021_ = l_Lean_MessageData_ofExpr(v_t_2936_);
v___x_3022_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
lean_inc_ref(v_s_2937_);
v___x_3024_ = l_Lean_MessageData_ofExpr(v_s_2937_);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_3018_, v___x_3025_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_dec_ref_known(v___x_3026_, 1);
v___y_2944_ = v_a_2938_;
v___y_2945_ = v_a_2939_;
v___y_2946_ = v_a_2940_;
v___y_2947_ = v_a_2941_;
goto v___jp_2943_;
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v_s_2937_);
lean_dec_ref(v_t_2936_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
v___jp_2943_:
{
lean_object* v___x_2948_; uint8_t v_unificationHints_2949_; 
v___x_2948_ = l_Lean_Meta_Context_config(v___y_2944_);
v_unificationHints_2949_ = lean_ctor_get_uint8(v___x_2948_, 5);
lean_dec_ref(v___x_2948_);
if (v_unificationHints_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
lean_dec_ref(v_s_2937_);
lean_dec_ref(v_t_2936_);
v___x_2950_ = lean_box(v_unificationHints_2949_);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
else
{
uint8_t v___x_2952_; 
v___x_2952_ = l_Lean_Expr_isMVar(v_t_2936_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v_env_2954_; lean_object* v___x_2955_; lean_object* v_ext_2956_; lean_object* v_toEnvExtension_2957_; lean_object* v_asyncMode_2958_; lean_object* v___x_2959_; lean_object* v_config_2960_; uint8_t v_trackZetaDelta_2961_; lean_object* v_zetaDeltaSet_2962_; lean_object* v_lctx_2963_; lean_object* v_localInstances_2964_; lean_object* v_defEqCtx_x3f_2965_; lean_object* v_synthPendingDepth_2966_; lean_object* v_canUnfold_x3f_2967_; uint8_t v_univApprox_2968_; uint8_t v_inTypeClassResolution_2969_; uint8_t v_cacheInferType_2970_; uint64_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2953_ = lean_st_ref_get(v___y_2947_);
v_env_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc_ref(v_env_2954_);
lean_dec(v___x_2953_);
v___x_2955_ = l_Lean_Meta_unificationHintExtension;
v_ext_2956_ = lean_ctor_get(v___x_2955_, 1);
v_toEnvExtension_2957_ = lean_ctor_get(v_ext_2956_, 0);
v_asyncMode_2958_ = lean_ctor_get(v_toEnvExtension_2957_, 2);
v___x_2959_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_2960_ = lean_ctor_get(v___x_2959_, 0);
v_trackZetaDelta_2961_ = lean_ctor_get_uint8(v___y_2944_, sizeof(void*)*7);
v_zetaDeltaSet_2962_ = lean_ctor_get(v___y_2944_, 1);
v_lctx_2963_ = lean_ctor_get(v___y_2944_, 2);
v_localInstances_2964_ = lean_ctor_get(v___y_2944_, 3);
v_defEqCtx_x3f_2965_ = lean_ctor_get(v___y_2944_, 4);
v_synthPendingDepth_2966_ = lean_ctor_get(v___y_2944_, 5);
v_canUnfold_x3f_2967_ = lean_ctor_get(v___y_2944_, 6);
v_univApprox_2968_ = lean_ctor_get_uint8(v___y_2944_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2969_ = lean_ctor_get_uint8(v___y_2944_, sizeof(void*)*7 + 2);
v_cacheInferType_2970_ = lean_ctor_get_uint8(v___y_2944_, sizeof(void*)*7 + 3);
v___x_2971_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2960_);
v___x_2972_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___x_2973_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2972_, v___x_2955_, v_env_2954_, v_asyncMode_2958_);
lean_inc_ref(v_config_2960_);
v___x_2974_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2974_, 0, v_config_2960_);
lean_ctor_set_uint64(v___x_2974_, sizeof(void*)*1, v___x_2971_);
lean_inc(v_canUnfold_x3f_2967_);
lean_inc(v_synthPendingDepth_2966_);
lean_inc(v_defEqCtx_x3f_2965_);
lean_inc_ref(v_localInstances_2964_);
lean_inc_ref(v_lctx_2963_);
lean_inc(v_zetaDeltaSet_2962_);
v___x_2975_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
lean_ctor_set(v___x_2975_, 1, v_zetaDeltaSet_2962_);
lean_ctor_set(v___x_2975_, 2, v_lctx_2963_);
lean_ctor_set(v___x_2975_, 3, v_localInstances_2964_);
lean_ctor_set(v___x_2975_, 4, v_defEqCtx_x3f_2965_);
lean_ctor_set(v___x_2975_, 5, v_synthPendingDepth_2966_);
lean_ctor_set(v___x_2975_, 6, v_canUnfold_x3f_2967_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*7, v_trackZetaDelta_2961_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*7 + 1, v_univApprox_2968_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2969_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*7 + 3, v_cacheInferType_2970_);
lean_inc_ref(v_t_2936_);
v___x_2976_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v___x_2973_, v_t_2936_, v___x_2975_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec_ref_known(v___x_2975_, 7);
lean_dec(v___x_2973_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2978_; size_t v_sz_2979_; size_t v___x_2980_; lean_object* v___x_2981_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2976_, 1);
v___x_2978_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_sz_2979_ = lean_array_size(v_a_2977_);
v___x_2980_ = ((size_t)0ULL);
v___x_2981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2936_, v_s_2937_, v_unificationHints_2949_, v_a_2977_, v_sz_2979_, v___x_2980_, v___x_2978_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v_a_2977_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2995_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2984_ = v___x_2981_;
v_isShared_2985_ = v_isSharedCheck_2995_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2981_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2995_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v_fst_2986_; 
v_fst_2986_ = lean_ctor_get(v_a_2982_, 0);
lean_inc(v_fst_2986_);
lean_dec(v_a_2982_);
if (lean_obj_tag(v_fst_2986_) == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2987_ = lean_box(v___x_2952_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v___x_2987_);
v___x_2989_ = v___x_2984_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
else
{
lean_object* v_val_2991_; lean_object* v___x_2993_; 
v_val_2991_ = lean_ctor_get(v_fst_2986_, 0);
lean_inc(v_val_2991_);
lean_dec_ref_known(v_fst_2986_, 1);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v_val_2991_);
v___x_2993_ = v___x_2984_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_val_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
v_a_2996_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2981_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2981_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec_ref(v_s_2937_);
lean_dec_ref(v_t_2936_);
v_a_3004_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2976_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2976_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
else
{
uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec_ref(v_s_2937_);
lean_dec_ref(v_t_2936_);
v___x_3012_ = 0;
v___x_3013_ = lean_box(v___x_3012_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___boxed(lean_object* v_t_3035_, lean_object* v_s_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Meta_tryUnificationHints(v_t_3035_, v_s_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
return v_res_3042_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = lean_unsigned_to_nat(2674080740u);
v___x_3044_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3045_ = l_Lean_Name_num___override(v___x_3044_, v___x_3043_);
return v___x_3045_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3047_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3048_ = l_Lean_Name_str___override(v___x_3047_, v___x_3046_);
return v___x_3048_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3050_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3051_ = l_Lean_Name_str___override(v___x_3050_, v___x_3049_);
return v___x_3051_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_unsigned_to_nat(2u);
v___x_3053_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3054_ = l_Lean_Name_num___override(v___x_3053_, v___x_3052_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3056_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__5));
v___x_3057_ = 0;
v___x_3058_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3059_ = l_Lean_registerTraceClass(v___x_3056_, v___x_3057_, v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
return v_res_3061_;
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
