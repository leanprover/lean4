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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty___redArg();
lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getResetPostponed___redArg(lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_recordExtGenAccess___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unificationHintExtension"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 204, 145, 124, 244, 133, 63, 146)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_UnificationHints_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "UnificationHint"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 112, 70, 159, 80, 199, 244, 3)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 201, 225, 55, 169, 192, 235, 23)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 76, 73, 18, 200, 34, 166, 102)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 195, 224, 136, 81, 175, 205, 78)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 1, 154, 40, 227, 230, 26, 25)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 208, 18, 32, 63, 140, 98, 77)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 91, 67, 57, 71, 246, 20, 20)}};
static const lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 2, 155, 161, 116, 126, 168, 23)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isDefEq"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_value;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hint"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_value;
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 173, 228, 229, 125, 117, 225, 10)}};
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 131, 150, 64, 79, 8, 33, 190)}};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3;
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4_value;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value;
static const lean_ctor_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7;
static const lean_string_object l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = " succeeded, applying constraints"};
static const lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8 = (const lean_object*)&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_value;
static lean_once_cell_t l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9;
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_8_ = l_Lean_Meta_DiscrTree_empty___redArg();
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12_spec__13___redArg(lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_x_29_, lean_object* v_x_30_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12___redArg(lean_object* v_n_57_, lean_object* v_k_58_, lean_object* v_v_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12_spec__13___redArg(v_n_57_, v___x_60_, v_k_58_, v_v_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg(lean_object* v_x_63_, size_t v_x_64_, size_t v_x_65_, lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_63_) == 0)
{
lean_object* v_es_68_; size_t v___x_69_; size_t v___x_70_; lean_object* v_j_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_es_68_ = lean_ctor_get(v_x_63_, 0);
v___x_69_ = ((size_t)31ULL);
v___x_70_ = lean_usize_land(v_x_64_, v___x_69_);
v_j_71_ = lean_usize_to_nat(v___x_70_);
v___x_72_ = lean_array_get_size(v_es_68_);
v___x_73_ = lean_nat_dec_lt(v_j_71_, v___x_72_);
if (v___x_73_ == 0)
{
lean_dec(v_j_71_);
lean_dec(v_x_67_);
lean_dec(v_x_66_);
return v_x_63_;
}
else
{
lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_112_; 
lean_inc_ref(v_es_68_);
v_isSharedCheck_112_ = !lean_is_exclusive(v_x_63_);
if (v_isSharedCheck_112_ == 0)
{
lean_object* v_unused_113_; 
v_unused_113_ = lean_ctor_get(v_x_63_, 0);
lean_dec(v_unused_113_);
v___x_75_ = v_x_63_;
v_isShared_76_ = v_isSharedCheck_112_;
goto v_resetjp_74_;
}
else
{
lean_dec(v_x_63_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_112_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v_v_77_; lean_object* v___x_78_; lean_object* v_xs_x27_79_; lean_object* v___y_81_; 
v_v_77_ = lean_array_fget(v_es_68_, v_j_71_);
v___x_78_ = lean_box(0);
v_xs_x27_79_ = lean_array_fset(v_es_68_, v_j_71_, v___x_78_);
switch(lean_obj_tag(v_v_77_))
{
case 0:
{
lean_object* v_key_86_; lean_object* v_val_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_97_; 
v_key_86_ = lean_ctor_get(v_v_77_, 0);
v_val_87_ = lean_ctor_get(v_v_77_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_v_77_);
if (v_isSharedCheck_97_ == 0)
{
v___x_89_ = v_v_77_;
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_val_87_);
lean_inc(v_key_86_);
lean_dec(v_v_77_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint8_t v___x_91_; 
v___x_91_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_66_, v_key_86_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_del_object(v___x_89_);
v___x_92_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_86_, v_val_87_, v_x_66_, v_x_67_);
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
v___y_81_ = v___x_93_;
goto v___jp_80_;
}
else
{
lean_object* v___x_95_; 
lean_dec(v_val_87_);
lean_dec(v_key_86_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_x_67_);
lean_ctor_set(v___x_89_, 0, v_x_66_);
v___x_95_ = v___x_89_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_x_66_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_x_67_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
v___y_81_ = v___x_95_;
goto v___jp_80_;
}
}
}
}
case 1:
{
lean_object* v_node_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_110_; 
v_node_98_ = lean_ctor_get(v_v_77_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v_v_77_);
if (v_isSharedCheck_110_ == 0)
{
v___x_100_ = v_v_77_;
v_isShared_101_ = v_isSharedCheck_110_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_node_98_);
lean_dec(v_v_77_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_110_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
size_t v___x_102_; size_t v___x_103_; size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_102_ = ((size_t)5ULL);
v___x_103_ = lean_usize_shift_right(v_x_64_, v___x_102_);
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_add(v_x_65_, v___x_104_);
v___x_106_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg(v_node_98_, v___x_103_, v___x_105_, v_x_66_, v_x_67_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_106_);
v___x_108_ = v___x_100_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
v___y_81_ = v___x_108_;
goto v___jp_80_;
}
}
}
default: 
{
lean_object* v___x_111_; 
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v_x_66_);
lean_ctor_set(v___x_111_, 1, v_x_67_);
v___y_81_ = v___x_111_;
goto v___jp_80_;
}
}
v___jp_80_:
{
lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_82_ = lean_array_fset(v_xs_x27_79_, v_j_71_, v___y_81_);
lean_dec(v_j_71_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_82_);
v___x_84_ = v___x_75_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
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
else
{
lean_object* v_ks_114_; lean_object* v_vs_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_133_; 
v_ks_114_ = lean_ctor_get(v_x_63_, 0);
v_vs_115_ = lean_ctor_get(v_x_63_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v_x_63_);
if (v_isSharedCheck_133_ == 0)
{
v___x_117_ = v_x_63_;
v_isShared_118_ = v_isSharedCheck_133_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_vs_115_);
lean_inc(v_ks_114_);
lean_dec(v_x_63_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_133_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_ks_114_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_vs_115_);
v___x_120_ = v_reuseFailAlloc_132_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v_newNode_121_; size_t v___x_122_; uint8_t v___x_123_; 
v_newNode_121_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12___redArg(v___x_120_, v_x_66_, v_x_67_);
v___x_122_ = ((size_t)7ULL);
v___x_123_ = lean_usize_dec_le(v___x_122_, v_x_65_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_121_);
v___x_125_ = lean_unsigned_to_nat(4u);
v___x_126_ = lean_nat_dec_lt(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
if (v___x_126_ == 0)
{
lean_object* v_ks_127_; lean_object* v_vs_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_ks_127_ = lean_ctor_get(v_newNode_121_, 0);
lean_inc_ref(v_ks_127_);
v_vs_128_ = lean_ctor_get(v_newNode_121_, 1);
lean_inc_ref(v_vs_128_);
lean_dec_ref(v_newNode_121_);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13___redArg(v_x_65_, v_ks_127_, v_vs_128_, v___x_129_, v___x_130_);
lean_dec_ref(v_vs_128_);
lean_dec_ref(v_ks_127_);
return v___x_131_;
}
else
{
return v_newNode_121_;
}
}
else
{
return v_newNode_121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13___redArg(size_t v_depth_134_, lean_object* v_keys_135_, lean_object* v_vals_136_, lean_object* v_i_137_, lean_object* v_entries_138_){
_start:
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = lean_array_get_size(v_keys_135_);
v___x_140_ = lean_nat_dec_lt(v_i_137_, v___x_139_);
if (v___x_140_ == 0)
{
lean_dec(v_i_137_);
return v_entries_138_;
}
else
{
lean_object* v_k_141_; lean_object* v_v_142_; uint64_t v___x_143_; size_t v_h_144_; size_t v___x_145_; lean_object* v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v_h_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_k_141_ = lean_array_fget_borrowed(v_keys_135_, v_i_137_);
v_v_142_ = lean_array_fget_borrowed(v_vals_136_, v_i_137_);
v___x_143_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_141_);
v_h_144_ = lean_uint64_to_usize(v___x_143_);
v___x_145_ = ((size_t)5ULL);
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v_depth_134_, v___x_147_);
v___x_149_ = lean_usize_mul(v___x_145_, v___x_148_);
v_h_150_ = lean_usize_shift_right(v_h_144_, v___x_149_);
v___x_151_ = lean_nat_add(v_i_137_, v___x_146_);
lean_dec(v_i_137_);
lean_inc(v_v_142_);
lean_inc(v_k_141_);
v___x_152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg(v_entries_138_, v_h_150_, v_depth_134_, v_k_141_, v_v_142_);
v_i_137_ = v___x_151_;
v_entries_138_ = v___x_152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13___redArg___boxed(lean_object* v_depth_154_, lean_object* v_keys_155_, lean_object* v_vals_156_, lean_object* v_i_157_, lean_object* v_entries_158_){
_start:
{
size_t v_depth_boxed_159_; lean_object* v_res_160_; 
v_depth_boxed_159_ = lean_unbox_usize(v_depth_154_);
lean_dec(v_depth_154_);
v_res_160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13___redArg(v_depth_boxed_159_, v_keys_155_, v_vals_156_, v_i_157_, v_entries_158_);
lean_dec_ref(v_vals_156_);
lean_dec_ref(v_keys_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
size_t v_x_2644__boxed_166_; size_t v_x_2645__boxed_167_; lean_object* v_res_168_; 
v_x_2644__boxed_166_ = lean_unbox_usize(v_x_162_);
lean_dec(v_x_162_);
v_x_2645__boxed_167_ = lean_unbox_usize(v_x_163_);
lean_dec(v_x_163_);
v_res_168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg(v_x_161_, v_x_2644__boxed_166_, v_x_2645__boxed_167_, v_x_164_, v_x_165_);
return v_res_168_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_169_, lean_object* v_b_170_){
_start:
{
lean_object* v_fst_171_; lean_object* v_fst_172_; uint8_t v___x_173_; 
v_fst_171_ = lean_ctor_get(v_a_169_, 0);
v_fst_172_ = lean_ctor_get(v_b_170_, 0);
v___x_173_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_171_, v_fst_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_a_174_, lean_object* v_b_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v_a_174_, v_b_175_);
lean_dec_ref(v_b_175_);
lean_dec_ref(v_a_174_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v___x_178_, lean_object* v_as_179_, lean_object* v_k_180_, lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_mid_185_; lean_object* v_midVal_186_; uint8_t v___x_187_; 
v___x_183_ = lean_nat_add(v_x_181_, v_x_182_);
v___x_184_ = lean_unsigned_to_nat(1u);
v_mid_185_ = lean_nat_shiftr(v___x_183_, v___x_184_);
lean_dec(v___x_183_);
v_midVal_186_ = lean_array_fget_borrowed(v_as_179_, v_mid_185_);
v___x_187_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v_midVal_186_, v_k_180_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
lean_dec(v_x_182_);
v___x_188_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v_k_180_, v_midVal_186_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
lean_dec(v_x_181_);
v___x_189_ = lean_array_get_size(v_as_179_);
v___x_190_ = lean_nat_dec_lt(v_mid_185_, v___x_189_);
if (v___x_190_ == 0)
{
lean_dec(v_mid_185_);
lean_dec_ref(v___x_178_);
return v_as_179_;
}
else
{
lean_object* v___x_191_; lean_object* v_xs_x27_192_; lean_object* v___x_193_; 
v___x_191_ = lean_box(0);
v_xs_x27_192_ = lean_array_fset(v_as_179_, v_mid_185_, v___x_191_);
v___x_193_ = lean_array_fset(v_xs_x27_192_, v_mid_185_, v___x_178_);
lean_dec(v_mid_185_);
return v___x_193_;
}
}
else
{
v_x_182_ = v_mid_185_;
goto _start;
}
}
else
{
uint8_t v___x_195_; 
v___x_195_ = lean_nat_dec_eq(v_mid_185_, v_x_181_);
if (v___x_195_ == 0)
{
lean_dec(v_x_181_);
v_x_181_ = v_mid_185_;
goto _start;
}
else
{
lean_object* v___x_197_; lean_object* v_j_198_; lean_object* v_as_199_; lean_object* v___x_200_; 
lean_dec(v_mid_185_);
lean_dec(v_x_182_);
v___x_197_ = lean_nat_add(v_x_181_, v___x_184_);
lean_dec(v_x_181_);
v_j_198_ = lean_array_get_size(v_as_179_);
v_as_199_ = lean_array_push(v_as_179_, v___x_178_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_197_, v_as_199_, v_j_198_);
lean_dec(v___x_197_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v___x_201_, lean_object* v_as_202_, lean_object* v_k_203_, lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v___x_201_, v_as_202_, v_k_203_, v_x_204_, v_x_205_);
lean_dec_ref(v_k_203_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(lean_object* v___x_207_, lean_object* v_as_208_, lean_object* v_k_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_210_ = lean_array_get_size(v_as_208_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_nat_dec_eq(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_array_fget_borrowed(v_as_208_, v___x_211_);
v___x_214_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v_k_209_, v___x_213_);
if (v___x_214_ == 0)
{
uint8_t v___x_215_; 
v___x_215_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v___x_213_, v_k_209_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; 
v___x_216_ = lean_nat_dec_lt(v___x_211_, v___x_210_);
if (v___x_216_ == 0)
{
lean_dec_ref(v___x_207_);
return v_as_208_;
}
else
{
lean_object* v___x_217_; lean_object* v_xs_x27_218_; lean_object* v___x_219_; 
v___x_217_ = lean_box(0);
v_xs_x27_218_ = lean_array_fset(v_as_208_, v___x_211_, v___x_217_);
v___x_219_ = lean_array_fset(v_xs_x27_218_, v___x_211_, v___x_207_);
return v___x_219_;
}
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = lean_nat_sub(v___x_210_, v___x_220_);
v___x_222_ = lean_array_fget_borrowed(v_as_208_, v___x_221_);
v___x_223_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v___x_222_, v_k_209_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; 
v___x_224_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v_k_209_, v___x_222_);
if (v___x_224_ == 0)
{
uint8_t v___x_225_; 
v___x_225_ = lean_nat_dec_lt(v___x_221_, v___x_210_);
if (v___x_225_ == 0)
{
lean_dec(v___x_221_);
lean_dec_ref(v___x_207_);
return v_as_208_;
}
else
{
lean_object* v___x_226_; lean_object* v_xs_x27_227_; lean_object* v___x_228_; 
v___x_226_ = lean_box(0);
v_xs_x27_227_ = lean_array_fset(v_as_208_, v___x_221_, v___x_226_);
v___x_228_ = lean_array_fset(v_xs_x27_227_, v___x_221_, v___x_207_);
lean_dec(v___x_221_);
return v___x_228_;
}
}
else
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v___x_207_, v_as_208_, v_k_209_, v___x_211_, v___x_221_);
return v___x_229_;
}
}
else
{
lean_object* v___x_230_; 
lean_dec(v___x_221_);
v___x_230_ = lean_array_push(v_as_208_, v___x_207_);
return v___x_230_;
}
}
}
else
{
lean_object* v_as_231_; lean_object* v___x_232_; 
v_as_231_ = lean_array_push(v_as_208_, v___x_207_);
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_211_, v_as_231_, v___x_210_);
return v___x_232_;
}
}
else
{
lean_object* v___x_233_; 
v___x_233_ = lean_array_push(v_as_208_, v___x_207_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___boxed(lean_object* v___x_234_, lean_object* v_as_235_, lean_object* v_k_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(v___x_234_, v_as_235_, v_k_236_);
lean_dec_ref(v_k_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__0(lean_object* v_i_238_, lean_object* v_keys_239_, lean_object* v_v_240_, lean_object* v_k_241_, lean_object* v_x_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_c_245_; lean_object* v___x_246_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_i_238_, v___x_243_);
v_c_245_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_c_245_, 0, v_keys_239_);
lean_ctor_set(v_c_245_, 1, v___x_244_);
lean_ctor_set(v_c_245_, 2, v_v_240_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_k_241_);
lean_ctor_set(v___x_246_, 1, v_c_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__0___boxed(lean_object* v_i_247_, lean_object* v_keys_248_, lean_object* v_v_249_, lean_object* v_k_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__0(v_i_247_, v_keys_248_, v_v_249_, v_k_250_, v_x_251_);
lean_dec(v_i_247_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5(lean_object* v_vs_253_, lean_object* v_v_254_, lean_object* v_i_255_){
_start:
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_array_get_size(v_vs_253_);
v___x_257_ = lean_nat_dec_lt(v_i_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_dec(v_i_255_);
v___x_258_ = lean_array_push(v_vs_253_, v_v_254_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_fget_borrowed(v_vs_253_, v_i_255_);
v___x_260_ = lean_name_eq(v_v_254_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_i_255_, v___x_261_);
lean_dec(v_i_255_);
v_i_255_ = v___x_262_;
goto _start;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = lean_array_fset(v_vs_253_, v_i_255_, v_v_254_);
lean_dec(v_i_255_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(lean_object* v_vs_265_, lean_object* v_v_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5(v_vs_265_, v_v_266_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_i_273_, lean_object* v_keys_274_, lean_object* v_v_275_, lean_object* v_k_276_, lean_object* v_as_277_, lean_object* v_k_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_mid_283_; lean_object* v_midVal_284_; uint8_t v___x_285_; 
v___x_281_ = lean_nat_add(v_x_279_, v_x_280_);
v___x_282_ = lean_unsigned_to_nat(1u);
v_mid_283_ = lean_nat_shiftr(v___x_281_, v___x_282_);
lean_dec(v___x_281_);
v_midVal_284_ = lean_array_fget(v_as_277_, v_mid_283_);
v___x_285_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v_midVal_284_, v_k_278_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
lean_dec(v_x_280_);
v___x_286_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v_k_278_, v_midVal_284_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
lean_dec(v_x_279_);
v___x_287_ = lean_array_get_size(v_as_277_);
v___x_288_ = lean_nat_dec_lt(v_mid_283_, v___x_287_);
if (v___x_288_ == 0)
{
lean_dec(v_midVal_284_);
lean_dec(v_mid_283_);
lean_dec(v_k_276_);
lean_dec(v_v_275_);
lean_dec_ref(v_keys_274_);
return v_as_277_;
}
else
{
lean_object* v_snd_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_301_; 
v_snd_289_ = lean_ctor_get(v_midVal_284_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_midVal_284_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_midVal_284_, 0);
lean_dec(v_unused_302_);
v___x_291_ = v_midVal_284_;
v_isShared_292_ = v_isSharedCheck_301_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_snd_289_);
lean_dec(v_midVal_284_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_301_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v_xs_x27_294_; lean_object* v___x_295_; lean_object* v_c_296_; lean_object* v___x_298_; 
v___x_293_ = lean_box(0);
v_xs_x27_294_ = lean_array_fset(v_as_277_, v_mid_283_, v___x_293_);
v___x_295_ = lean_nat_add(v_i_273_, v___x_282_);
v_c_296_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_274_, v_v_275_, v___x_295_, v_snd_289_);
lean_dec(v___x_295_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_c_296_);
lean_ctor_set(v___x_291_, 0, v_k_276_);
v___x_298_ = v___x_291_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_k_276_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_c_296_);
v___x_298_ = v_reuseFailAlloc_300_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; 
v___x_299_ = lean_array_fset(v_xs_x27_294_, v_mid_283_, v___x_298_);
lean_dec(v_mid_283_);
return v___x_299_;
}
}
}
}
else
{
lean_dec(v_midVal_284_);
v_x_280_ = v_mid_283_;
goto _start;
}
}
else
{
uint8_t v___x_304_; 
lean_dec(v_midVal_284_);
v___x_304_ = lean_nat_dec_eq(v_mid_283_, v_x_279_);
if (v___x_304_ == 0)
{
lean_dec(v_x_279_);
v_x_279_ = v_mid_283_;
goto _start;
}
else
{
lean_object* v___x_306_; lean_object* v_c_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_j_310_; lean_object* v_as_311_; lean_object* v___x_312_; 
lean_dec(v_mid_283_);
lean_dec(v_x_280_);
v___x_306_ = lean_nat_add(v_i_273_, v___x_282_);
v_c_307_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_c_307_, 0, v_keys_274_);
lean_ctor_set(v_c_307_, 1, v___x_306_);
lean_ctor_set(v_c_307_, 2, v_v_275_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_k_276_);
lean_ctor_set(v___x_308_, 1, v_c_307_);
v___x_309_ = lean_nat_add(v_x_279_, v___x_282_);
lean_dec(v_x_279_);
v_j_310_ = lean_array_get_size(v_as_277_);
v_as_311_ = lean_array_push(v_as_277_, v___x_308_);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_309_, v_as_311_, v_j_310_);
lean_dec(v___x_309_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3(lean_object* v_i_313_, lean_object* v_keys_314_, lean_object* v_v_315_, lean_object* v_k_316_, lean_object* v_as_317_, lean_object* v_k_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_319_ = lean_array_get_size(v_as_317_);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_nat_dec_eq(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_array_fget_borrowed(v_as_317_, v___x_320_);
v___x_323_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v_k_318_, v___x_322_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; 
v___x_324_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v___x_322_, v_k_318_);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = lean_nat_dec_lt(v___x_320_, v___x_319_);
if (v___x_325_ == 0)
{
lean_dec(v_k_316_);
lean_dec(v_v_315_);
lean_dec_ref(v_keys_314_);
return v_as_317_;
}
else
{
lean_object* v___x_326_; lean_object* v_xs_x27_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_inc(v___x_322_);
v___x_326_ = lean_box(0);
v_xs_x27_327_ = lean_array_fset(v_as_317_, v___x_320_, v___x_326_);
v___x_328_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__2(v_i_313_, v_keys_314_, v_v_315_, v_k_316_, v___x_322_);
v___x_329_ = lean_array_fset(v_xs_x27_327_, v___x_320_, v___x_328_);
return v___x_329_;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_sub(v___x_319_, v___x_330_);
v___x_332_ = lean_array_fget_borrowed(v_as_317_, v___x_331_);
v___x_333_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v___x_332_, v_k_318_);
if (v___x_333_ == 0)
{
uint8_t v___x_334_; 
v___x_334_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___lam__0(v_k_318_, v___x_332_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
v___x_335_ = lean_nat_dec_lt(v___x_331_, v___x_319_);
if (v___x_335_ == 0)
{
lean_dec(v___x_331_);
lean_dec(v_k_316_);
lean_dec(v_v_315_);
lean_dec_ref(v_keys_314_);
return v_as_317_;
}
else
{
lean_object* v___x_336_; lean_object* v_xs_x27_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_inc(v___x_332_);
v___x_336_ = lean_box(0);
v_xs_x27_337_ = lean_array_fset(v_as_317_, v___x_331_, v___x_336_);
v___x_338_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__2(v_i_313_, v_keys_314_, v_v_315_, v_k_316_, v___x_332_);
v___x_339_ = lean_array_fset(v_xs_x27_337_, v___x_331_, v___x_338_);
lean_dec(v___x_331_);
return v___x_339_;
}
}
else
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7___redArg(v_i_313_, v_keys_314_, v_v_315_, v_k_316_, v_as_317_, v_k_318_, v___x_320_, v___x_331_);
return v___x_340_;
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v___x_331_);
v___x_341_ = lean_box(0);
v___x_342_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__0(v_i_313_, v_keys_314_, v_v_315_, v_k_316_, v___x_341_);
v___x_343_ = lean_array_push(v_as_317_, v___x_342_);
return v___x_343_;
}
}
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_as_346_; lean_object* v___x_347_; 
v___x_344_ = lean_box(0);
v___x_345_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__0(v_i_313_, v_keys_314_, v_v_315_, v_k_316_, v___x_344_);
v_as_346_ = lean_array_push(v_as_317_, v___x_345_);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_320_, v_as_346_, v___x_319_);
return v___x_347_;
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_box(0);
v___x_349_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__0(v_i_313_, v_keys_314_, v_v_315_, v_k_316_, v___x_348_);
v___x_350_ = lean_array_push(v_as_317_, v___x_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object* v_keys_351_, lean_object* v_v_352_, lean_object* v_i_353_, lean_object* v_t_354_){
_start:
{
lean_object* v_val_356_; 
switch(lean_obj_tag(v_t_354_))
{
case 2:
{
lean_object* v___x_412_; 
v___x_412_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_354_);
v_val_356_ = v___x_412_;
goto v___jp_355_;
}
case 3:
{
lean_object* v___x_413_; 
v___x_413_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_354_);
v_val_356_ = v___x_413_;
goto v___jp_355_;
}
default: 
{
v_val_356_ = v_t_354_;
goto v___jp_355_;
}
}
v___jp_355_:
{
if (lean_obj_tag(v_val_356_) == 0)
{
lean_object* v_key_357_; lean_object* v_child_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_392_; 
v_key_357_ = lean_ctor_get(v_val_356_, 0);
v_child_358_ = lean_ctor_get(v_val_356_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v_val_356_);
if (v_isSharedCheck_392_ == 0)
{
v___x_360_ = v_val_356_;
v_isShared_361_ = v_isSharedCheck_392_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_child_358_);
lean_inc(v_key_357_);
lean_dec(v_val_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_392_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_array_get_size(v_keys_351_);
v___x_363_ = lean_nat_dec_lt(v_i_353_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
lean_dec_ref(v_keys_351_);
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = lean_mk_empty_array_with_capacity(v___x_364_);
lean_inc_ref(v___x_365_);
v___x_366_ = lean_array_push(v___x_365_, v_v_352_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_key_357_);
lean_ctor_set(v___x_367_, 1, v_child_358_);
v___x_368_ = lean_array_push(v___x_365_, v___x_367_);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
lean_ctor_set(v___x_360_, 1, v___x_368_);
lean_ctor_set(v___x_360_, 0, v___x_366_);
v___x_370_ = v___x_360_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_array_fget_borrowed(v_keys_351_, v_i_353_);
v___x_373_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_372_, v_key_357_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
lean_inc(v___x_372_);
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__0));
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_key_357_);
lean_ctor_set(v___x_375_, 1, v_child_358_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_mk_empty_array_with_capacity(v___x_376_);
v___x_378_ = lean_array_push(v___x_377_, v___x_375_);
v___x_379_ = lean_nat_add(v_i_353_, v___x_376_);
v___x_380_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_380_, 0, v_keys_351_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
lean_ctor_set(v___x_380_, 2, v_v_352_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_372_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
lean_inc_ref(v___x_381_);
v___x_382_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(v___x_381_, v___x_378_, v___x_381_);
lean_dec_ref_known(v___x_381_, 2);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
lean_ctor_set(v___x_360_, 1, v___x_382_);
lean_ctor_set(v___x_360_, 0, v___x_374_);
v___x_384_ = v___x_360_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_i_353_, v___x_386_);
v___x_388_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_351_, v_v_352_, v___x_387_, v_child_358_);
lean_dec(v___x_387_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_388_);
v___x_390_ = v___x_360_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_key_357_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
else
{
lean_object* v_vs_393_; lean_object* v_children_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_411_; 
v_vs_393_ = lean_ctor_get(v_val_356_, 0);
v_children_394_ = lean_ctor_get(v_val_356_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_val_356_);
if (v_isSharedCheck_411_ == 0)
{
v___x_396_ = v_val_356_;
v_isShared_397_ = v_isSharedCheck_411_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_children_394_);
lean_inc(v_vs_393_);
lean_dec(v_val_356_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_411_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_array_get_size(v_keys_351_);
v___x_399_ = lean_nat_dec_lt(v_i_353_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_402_; 
lean_dec_ref(v_keys_351_);
v___x_400_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(v_vs_393_, v_v_352_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_400_);
v___x_402_ = v___x_396_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_children_394_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
lean_object* v_k_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_c_407_; lean_object* v___x_409_; 
v_k_404_ = lean_array_fget(v_keys_351_, v_i_353_);
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__1));
lean_inc(v_k_404_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_k_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v_c_407_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3(v_i_353_, v_keys_351_, v_v_352_, v_k_404_, v_children_394_, v___x_406_);
lean_dec_ref_known(v___x_406_, 2);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v_c_407_);
v___x_409_ = v___x_396_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_vs_393_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_c_407_);
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
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__2(lean_object* v_i_414_, lean_object* v_keys_415_, lean_object* v_v_416_, lean_object* v_k_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_snd_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_429_; 
v_snd_419_ = lean_ctor_get(v_x_418_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v_x_418_, 0);
lean_dec(v_unused_430_);
v___x_421_ = v_x_418_;
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snd_419_);
lean_dec(v_x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_c_425_; lean_object* v___x_427_; 
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_add(v_i_414_, v___x_423_);
v_c_425_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_415_, v_v_416_, v___x_424_, v_snd_419_);
lean_dec(v___x_424_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v_c_425_);
lean_ctor_set(v___x_421_, 0, v_k_417_);
v___x_427_ = v___x_421_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_k_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_c_425_);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__2___boxed(lean_object* v_i_431_, lean_object* v_keys_432_, lean_object* v_v_433_, lean_object* v_k_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___lam__2(v_i_431_, v_keys_432_, v_v_433_, v_k_434_, v_x_435_);
lean_dec(v_i_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_i_437_, lean_object* v_keys_438_, lean_object* v_v_439_, lean_object* v_k_440_, lean_object* v_as_441_, lean_object* v_k_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7___redArg(v_i_437_, v_keys_438_, v_v_439_, v_k_440_, v_as_441_, v_k_442_, v_x_443_, v_x_444_);
lean_dec_ref(v_k_442_);
lean_dec(v_i_437_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3___boxed(lean_object* v_i_446_, lean_object* v_keys_447_, lean_object* v_v_448_, lean_object* v_k_449_, lean_object* v_as_450_, lean_object* v_k_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3(v_i_446_, v_keys_447_, v_v_448_, v_k_449_, v_as_450_, v_k_451_);
lean_dec_ref(v_k_451_);
lean_dec(v_i_446_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object* v_keys_453_, lean_object* v_v_454_, lean_object* v_i_455_, lean_object* v_t_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_453_, v_v_454_, v_i_455_, v_t_456_);
lean_dec(v_i_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(lean_object* v_keys_458_, lean_object* v_v_459_, lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_462_, 0, v_keys_458_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_ctor_set(v___x_462_, 2, v_v_459_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
else
{
lean_object* v_val_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_473_; 
v_val_464_ = lean_ctor_get(v_x_460_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_x_460_);
if (v_isSharedCheck_473_ == 0)
{
v___x_466_ = v_x_460_;
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_val_464_);
lean_dec(v_x_460_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_458_, v_v_459_, v___x_468_, v_val_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_469_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10(lean_object* v_xs_474_, lean_object* v_v_475_, lean_object* v_i_476_){
_start:
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_array_get_size(v_xs_474_);
v___x_478_ = lean_nat_dec_lt(v_i_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec(v_i_476_);
v___x_479_ = lean_box(0);
return v___x_479_;
}
else
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_array_fget_borrowed(v_xs_474_, v_i_476_);
v___x_481_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_480_, v_v_475_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_add(v_i_476_, v___x_482_);
lean_dec(v_i_476_);
v_i_476_ = v___x_483_;
goto _start;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v_i_476_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10___boxed(lean_object* v_xs_486_, lean_object* v_v_487_, lean_object* v_i_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10(v_xs_486_, v_v_487_, v_i_488_);
lean_dec(v_v_487_);
lean_dec_ref(v_xs_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5(lean_object* v_xs_490_, lean_object* v_v_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10(v_xs_490_, v_v_491_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___boxed(lean_object* v_xs_494_, lean_object* v_v_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5(v_xs_494_, v_v_495_);
lean_dec(v_v_495_);
lean_dec_ref(v_xs_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(lean_object* v_keys_497_, lean_object* v_v_498_, lean_object* v_x_499_, size_t v_x_500_, size_t v_x_501_, lean_object* v_x_502_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
lean_object* v_es_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v_j_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_es_503_ = lean_ctor_get(v_x_499_, 0);
v___x_504_ = ((size_t)31ULL);
v___x_505_ = lean_usize_land(v_x_500_, v___x_504_);
v_j_506_ = lean_usize_to_nat(v___x_505_);
v___x_507_ = lean_array_get_size(v_es_503_);
v___x_508_ = lean_nat_dec_lt(v_j_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v_j_506_);
lean_dec(v_x_502_);
lean_dec(v_v_498_);
lean_dec_ref(v_keys_497_);
return v_x_499_;
}
else
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_576_; 
lean_inc_ref(v_es_503_);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_x_499_, 0);
lean_dec(v_unused_577_);
v___x_510_ = v_x_499_;
v_isShared_511_ = v_isSharedCheck_576_;
goto v_resetjp_509_;
}
else
{
lean_dec(v_x_499_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_576_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_v_512_; lean_object* v___x_513_; lean_object* v_xs_x27_514_; lean_object* v___y_516_; 
v_v_512_ = lean_array_fget(v_es_503_, v_j_506_);
v___x_513_ = lean_box(0);
v_xs_x27_514_ = lean_array_fset(v_es_503_, v_j_506_, v___x_513_);
switch(lean_obj_tag(v_v_512_))
{
case 0:
{
lean_object* v_key_521_; lean_object* v_val_522_; uint8_t v___x_523_; 
v_key_521_ = lean_ctor_get(v_v_512_, 0);
v_val_522_ = lean_ctor_get(v_v_512_, 1);
v___x_523_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_502_, v_key_521_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_box(0);
v___x_525_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_497_, v_v_498_, v___x_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_dec(v_x_502_);
v___y_516_ = v_v_512_;
goto v___jp_515_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_534_; 
lean_inc(v_val_522_);
lean_inc(v_key_521_);
lean_dec_ref_known(v_v_512_, 2);
v_val_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_534_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_521_, v_val_522_, v_x_502_, v_val_526_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_530_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v___y_516_ = v___x_532_;
goto v___jp_515_;
}
}
}
}
else
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_545_; 
lean_inc(v_val_522_);
v_isSharedCheck_545_ = !lean_is_exclusive(v_v_512_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; 
v_unused_546_ = lean_ctor_get(v_v_512_, 1);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_v_512_, 0);
lean_dec(v_unused_547_);
v___x_536_ = v_v_512_;
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
else
{
lean_dec(v_v_512_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v_val_522_);
v___x_539_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_497_, v_v_498_, v___x_538_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v___x_540_; 
lean_del_object(v___x_536_);
lean_dec(v_x_502_);
v___x_540_ = lean_box(2);
v___y_516_ = v___x_540_;
goto v___jp_515_;
}
else
{
lean_object* v_val_541_; lean_object* v___x_543_; 
v_val_541_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___x_539_, 1);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v_val_541_);
lean_ctor_set(v___x_536_, 0, v_x_502_);
v___x_543_ = v___x_536_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_x_502_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_val_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
v___y_516_ = v___x_543_;
goto v___jp_515_;
}
}
}
}
}
case 1:
{
lean_object* v_node_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_571_; 
v_node_548_ = lean_ctor_get(v_v_512_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v_v_512_);
if (v_isSharedCheck_571_ == 0)
{
v___x_550_ = v_v_512_;
v_isShared_551_ = v_isSharedCheck_571_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_node_548_);
lean_dec(v_v_512_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_571_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; lean_object* v_newNode_556_; lean_object* v___x_557_; 
v___x_552_ = ((size_t)5ULL);
v___x_553_ = lean_usize_shift_right(v_x_500_, v___x_552_);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_x_501_, v___x_554_);
v_newNode_556_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(v_keys_497_, v_v_498_, v_node_548_, v___x_553_, v___x_555_, v_x_502_);
lean_inc_ref(v_newNode_556_);
v___x_557_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_556_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_559_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v_newNode_556_);
v___x_559_ = v___x_550_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_newNode_556_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
v___y_516_ = v___x_559_;
goto v___jp_515_;
}
}
else
{
lean_object* v_val_561_; lean_object* v_fst_562_; lean_object* v_snd_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v_newNode_556_);
lean_del_object(v___x_550_);
v_val_561_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_561_);
lean_dec_ref_known(v___x_557_, 1);
v_fst_562_ = lean_ctor_get(v_val_561_, 0);
v_snd_563_ = lean_ctor_get(v_val_561_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_val_561_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v_val_561_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snd_563_);
lean_inc(v_fst_562_);
lean_dec(v_val_561_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_fst_562_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_snd_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
v___y_516_ = v___x_568_;
goto v___jp_515_;
}
}
}
}
}
default: 
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_box(0);
v___x_573_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_497_, v_v_498_, v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_dec(v_x_502_);
v___y_516_ = v_v_512_;
goto v___jp_515_;
}
else
{
lean_object* v_val_574_; lean_object* v___x_575_; 
v_val_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_x_502_);
lean_ctor_set(v___x_575_, 1, v_val_574_);
v___y_516_ = v___x_575_;
goto v___jp_515_;
}
}
}
v___jp_515_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_array_fset(v_xs_x27_514_, v_j_506_, v___y_516_);
lean_dec(v_j_506_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_517_);
v___x_519_ = v___x_510_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
else
{
lean_object* v_ks_578_; lean_object* v_vs_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_612_; 
v_ks_578_ = lean_ctor_get(v_x_499_, 0);
v_vs_579_ = lean_ctor_get(v_x_499_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_612_ == 0)
{
v___x_581_ = v_x_499_;
v_isShared_582_ = v_isSharedCheck_612_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_vs_579_);
lean_inc(v_ks_578_);
lean_dec(v_x_499_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_612_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; 
v___x_583_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5(v_ks_578_, v_x_502_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_585_; 
if (v_isShared_582_ == 0)
{
v___x_585_ = v___x_581_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_ks_578_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_vs_579_);
v___x_585_ = v_reuseFailAlloc_590_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_box(0);
v___x_587_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_497_, v_v_498_, v___x_586_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_dec(v_x_502_);
return v___x_585_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_589_; 
v_val_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_val_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg(v___x_585_, v_x_500_, v_x_501_, v_x_502_, v_val_588_);
return v___x_589_;
}
}
}
else
{
lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_611_; 
v_val_591_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_611_ == 0)
{
v___x_593_ = v___x_583_;
v_isShared_594_ = v_isSharedCheck_611_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_dec(v___x_583_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_611_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_v_x27_595_; lean_object* v_keys_596_; lean_object* v_vals_597_; lean_object* v___x_599_; 
v_v_x27_595_ = lean_array_fget(v_vs_579_, v_val_591_);
lean_inc(v_val_591_);
v_keys_596_ = l_Array_eraseIdx___redArg(v_ks_578_, v_val_591_);
v_vals_597_ = l_Array_eraseIdx___redArg(v_vs_579_, v_val_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v_v_x27_595_);
v___x_599_ = v___x_593_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_v_x27_595_);
v___x_599_ = v_reuseFailAlloc_610_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_497_, v_v_498_, v___x_599_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v___x_602_; 
lean_dec(v_x_502_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_vals_597_);
lean_ctor_set(v___x_581_, 0, v_keys_596_);
v___x_602_ = v___x_581_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_keys_596_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_vals_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
else
{
lean_object* v_val_604_; lean_object* v_keys_605_; lean_object* v_vals_606_; lean_object* v___x_608_; 
v_val_604_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v___x_600_, 1);
v_keys_605_ = lean_array_push(v_keys_596_, v_x_502_);
v_vals_606_ = lean_array_push(v_vals_597_, v_val_604_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_vals_606_);
lean_ctor_set(v___x_581_, 0, v_keys_605_);
v___x_608_ = v___x_581_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_keys_605_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_vals_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___boxed(lean_object* v_keys_613_, lean_object* v_v_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
size_t v_x_3234__boxed_619_; size_t v_x_3235__boxed_620_; lean_object* v_res_621_; 
v_x_3234__boxed_619_ = lean_unbox_usize(v_x_616_);
lean_dec(v_x_616_);
v_x_3235__boxed_620_ = lean_unbox_usize(v_x_617_);
lean_dec(v_x_617_);
v_res_621_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(v_keys_613_, v_v_614_, v_x_615_, v_x_3234__boxed_619_, v_x_3235__boxed_620_, v_x_618_);
return v_res_621_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Meta_DiscrTree_instInhabited___redArg();
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(lean_object* v_msg_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0);
v___x_625_ = lean_panic_fn_borrowed(v___x_624_, v_msg_623_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_629_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2));
v___x_630_ = lean_unsigned_to_nat(23u);
v___x_631_ = lean_unsigned_to_nat(209u);
v___x_632_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1));
v___x_633_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0));
v___x_634_ = l_mkPanicMessageWithDecl(v___x_633_, v___x_632_, v___x_631_, v___x_630_, v___x_629_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(lean_object* v_d_635_, lean_object* v_keys_636_, lean_object* v_v_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_array_get_size(v_keys_636_);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_nat_dec_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v_k_642_; uint64_t v___x_643_; size_t v_h_644_; size_t v___x_645_; lean_object* v___x_646_; 
v___x_641_ = lean_box(0);
v_k_642_ = lean_array_get(v___x_641_, v_keys_636_, v___x_639_);
v___x_643_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_642_);
v_h_644_ = lean_uint64_to_usize(v___x_643_);
v___x_645_ = ((size_t)1ULL);
v___x_646_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(v_keys_636_, v_v_637_, v_d_635_, v_h_644_, v___x_645_, v_k_642_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_v_637_);
lean_dec_ref(v_keys_636_);
lean_dec_ref(v_d_635_);
v___x_647_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3);
v___x_648_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v___x_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* v_hints_649_, lean_object* v_e_650_){
_start:
{
lean_object* v_keys_651_; lean_object* v_val_652_; lean_object* v___x_653_; 
v_keys_651_ = lean_ctor_get(v_e_650_, 0);
lean_inc_ref(v_keys_651_);
v_val_652_ = lean_ctor_get(v_e_650_, 1);
lean_inc(v_val_652_);
lean_dec_ref(v_e_650_);
v___x_653_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_hints_649_, v_keys_651_, v_val_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, size_t v_x_656_, size_t v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___redArg(v_x_655_, v_x_656_, v_x_657_, v_x_658_, v_x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b2_661_, lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
size_t v_x_3502__boxed_667_; size_t v_x_3503__boxed_668_; lean_object* v_res_669_; 
v_x_3502__boxed_667_ = lean_unbox_usize(v_x_663_);
lean_dec(v_x_663_);
v_x_3503__boxed_668_ = lean_unbox_usize(v_x_664_);
lean_dec(v_x_664_);
v_res_669_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6(v_00_u03b2_661_, v_x_662_, v_x_3502__boxed_667_, v_x_3503__boxed_668_, v_x_665_, v_x_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(lean_object* v___x_670_, lean_object* v_as_671_, lean_object* v_k_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v___x_670_, v_as_671_, v_k_672_, v_x_673_, v_x_674_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v___x_678_, lean_object* v_as_679_, lean_object* v_k_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(v___x_678_, v_as_679_, v_k_680_, v_x_681_, v_x_682_, v_x_683_, v_x_684_);
lean_dec_ref(v_k_680_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7(lean_object* v_i_686_, lean_object* v_keys_687_, lean_object* v_v_688_, lean_object* v_k_689_, lean_object* v_as_690_, lean_object* v_k_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7___redArg(v_i_686_, v_keys_687_, v_v_688_, v_k_689_, v_as_690_, v_k_691_, v_x_692_, v_x_693_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_i_697_, lean_object* v_keys_698_, lean_object* v_v_699_, lean_object* v_k_700_, lean_object* v_as_701_, lean_object* v_k_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__3_spec__7(v_i_697_, v_keys_698_, v_v_699_, v_k_700_, v_as_701_, v_k_702_, v_x_703_, v_x_704_, v_x_705_, v_x_706_);
lean_dec_ref(v_k_702_);
lean_dec(v_i_697_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12(lean_object* v_00_u03b2_708_, lean_object* v_n_709_, lean_object* v_k_710_, lean_object* v_v_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12___redArg(v_n_709_, v_k_710_, v_v_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13(lean_object* v_00_u03b2_713_, size_t v_depth_714_, lean_object* v_keys_715_, lean_object* v_vals_716_, lean_object* v_heq_717_, lean_object* v_i_718_, lean_object* v_entries_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13___redArg(v_depth_714_, v_keys_715_, v_vals_716_, v_i_718_, v_entries_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13___boxed(lean_object* v_00_u03b2_721_, lean_object* v_depth_722_, lean_object* v_keys_723_, lean_object* v_vals_724_, lean_object* v_heq_725_, lean_object* v_i_726_, lean_object* v_entries_727_){
_start:
{
size_t v_depth_boxed_728_; lean_object* v_res_729_; 
v_depth_boxed_728_ = lean_unbox_usize(v_depth_722_);
lean_dec(v_depth_722_);
v_res_729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__13(v_00_u03b2_721_, v_depth_boxed_728_, v_keys_723_, v_vals_724_, v_heq_725_, v_i_726_, v_entries_727_);
lean_dec_ref(v_vals_724_);
lean_dec_ref(v_keys_723_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12_spec__13(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__6_spec__12_spec__13___redArg(v_x_731_, v_x_732_, v_x_733_, v_x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(lean_object* v___y_736_){
_start:
{
lean_inc_ref(v___y_736_);
return v___y_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(v___y_737_);
lean_dec_ref(v___y_737_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(lean_object* v_x_739_, lean_object* v_a_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_a_740_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object* v_x_744_, lean_object* v_a_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(v_x_744_, v_a_745_, v___y_746_);
lean_dec_ref(v___y_746_);
lean_dec_ref(v_x_744_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(lean_object* v_x_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v_a_750_);
lean_inc_ref_n(v___x_751_, 2);
v___x_752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
lean_ctor_set(v___x_752_, 2, v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object* v_x_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(v_x_753_, v_a_754_);
lean_dec_ref(v_x_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(lean_object* v___x_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object* v___x_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(v___x_759_);
return v_res_761_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_773_; lean_object* v___f_774_; 
v___x_773_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___f_774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__3_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_774_, 0, v___x_773_);
return v___f_774_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___x_778_; 
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_));
v___f_776_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_));
v___f_777_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_);
v___x_778_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedGlobals___boxed), 9, 6);
lean_closure_set(v___x_778_, 0, lean_box(0));
lean_closure_set(v___x_778_, 1, lean_box(0));
lean_closure_set(v___x_778_, 2, lean_box(0));
lean_closure_set(v___x_778_, 3, v___f_777_);
lean_closure_set(v___x_778_, 4, v___f_776_);
lean_closure_set(v___x_778_, 5, v___x_775_);
return v___x_778_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; uint8_t v___x_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_779_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_);
v___x_780_ = lean_box(0);
v___x_781_ = 0;
v___x_782_ = 1;
v___f_783_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_));
v___f_784_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_));
v___x_785_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_));
v___x_787_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_));
v___x_788_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
lean_ctor_set(v___x_788_, 2, v___x_786_);
lean_ctor_set(v___x_788_, 3, v___x_785_);
lean_ctor_set(v___x_788_, 4, v___f_784_);
lean_ctor_set(v___x_788_, 5, v___f_783_);
lean_ctor_set(v___x_788_, 6, v___x_780_);
lean_ctor_set(v___x_788_, 7, v___x_779_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*8, v___x_782_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*8 + 1, v___x_781_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_);
v___x_791_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2____boxed(lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_();
return v_res_793_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object* v_e_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_801_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1));
v___x_802_ = lean_unsigned_to_nat(3u);
v___x_803_ = l_Lean_Expr_isAppOfArity(v_e_800_, v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_804_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3);
v___x_805_ = l_Lean_indentExpr(v_e_800_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_808_ = l_Lean_Expr_appFn_x21(v_e_800_);
v___x_809_ = l_Lean_Expr_appArg_x21(v___x_808_);
lean_dec_ref(v___x_808_);
v___x_810_ = l_Lean_Expr_appArg_x21(v_e_800_);
lean_dec_ref(v_e_800_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object* v_e_816_, lean_object* v_cs_817_){
_start:
{
if (lean_obj_tag(v_e_816_) == 7)
{
lean_object* v_binderType_818_; lean_object* v_body_819_; lean_object* v___x_820_; 
v_binderType_818_ = lean_ctor_get(v_e_816_, 1);
v_body_819_ = lean_ctor_get(v_e_816_, 2);
lean_inc_ref(v_binderType_818_);
v___x_820_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_binderType_818_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref_known(v_e_816_, 3);
lean_dec_ref(v_cs_817_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_842_; 
v_a_829_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_842_ == 0)
{
v___x_831_ = v___x_820_;
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_820_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_Expr_hasLooseBVars(v_body_819_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_inc_ref(v_body_819_);
lean_del_object(v___x_831_);
lean_dec_ref_known(v_e_816_, 3);
v___x_834_ = lean_array_push(v_cs_817_, v_a_829_);
v_e_816_ = v_body_819_;
v_cs_817_ = v___x_834_;
goto _start;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
lean_dec(v_a_829_);
lean_dec_ref(v_cs_817_);
v___x_836_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1);
v___x_837_ = l_Lean_indentExpr(v_e_816_);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
lean_ctor_set(v___x_831_, 0, v___x_838_);
v___x_840_ = v___x_831_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
else
{
lean_object* v___x_843_; 
v___x_843_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_e_816_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v_cs_817_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_861_; 
v_a_852_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_861_ == 0)
{
v___x_854_ = v___x_843_;
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_843_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = lean_array_to_list(v_cs_817_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_a_852_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object* v_e_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0));
v___x_866_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(v_e_864_, v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(lean_object* v_msgData_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; lean_object* v_env_874_; uint8_t v___x_875_; lean_object* v_env_876_; lean_object* v___x_877_; lean_object* v_toCold_878_; lean_object* v_mctx_879_; lean_object* v_lctx_880_; lean_object* v_options_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_873_ = lean_st_ref_get(v___y_871_);
v_env_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc_ref(v_env_874_);
lean_dec(v___x_873_);
v___x_875_ = 0;
v_env_876_ = l_Lean_Environment_setRecordingDeps(v_env_874_, v___x_875_);
v___x_877_ = lean_st_ref_get(v___y_869_);
v_toCold_878_ = lean_ctor_get(v___y_870_, 0);
v_mctx_879_ = lean_ctor_get(v___x_877_, 0);
lean_inc_ref(v_mctx_879_);
lean_dec(v___x_877_);
v_lctx_880_ = lean_ctor_get(v___y_868_, 2);
v_options_881_ = lean_ctor_get(v_toCold_878_, 2);
lean_inc_ref(v_options_881_);
lean_inc_ref(v_lctx_880_);
v___x_882_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_882_, 0, v_env_876_);
lean_ctor_set(v___x_882_, 1, v_mctx_879_);
lean_ctor_set(v___x_882_, 2, v_lctx_880_);
lean_ctor_set(v___x_882_, 3, v_options_881_);
v___x_883_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v_msgData_867_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object* v_msgData_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msgData_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(lean_object* v_msg_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_ref_898_; lean_object* v___x_899_; lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_908_; 
v_ref_898_ = lean_ctor_get(v___y_895_, 2);
v___x_899_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_908_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
lean_inc(v_ref_898_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_ref_898_);
lean_ctor_set(v___x_904_, 1, v_a_900_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 1);
lean_ctor_set(v___x_902_, 0, v___x_904_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg___boxed(lean_object* v_msg_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_915_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0));
v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
return v___x_918_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(lean_object* v_as_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
if (lean_obj_tag(v_as_922_) == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_box(0);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
else
{
lean_object* v_head_930_; lean_object* v_tail_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_965_; 
v_head_930_ = lean_ctor_get(v_as_922_, 0);
v_tail_931_ = lean_ctor_get(v_as_922_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_as_922_);
if (v_isSharedCheck_965_ == 0)
{
v___x_933_ = v_as_922_;
v_isShared_934_ = v_isSharedCheck_965_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_tail_931_);
lean_inc(v_head_930_);
lean_dec(v_as_922_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_965_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_lhs_935_; lean_object* v_rhs_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_964_; 
v_lhs_935_ = lean_ctor_get(v_head_930_, 0);
v_rhs_936_ = lean_ctor_get(v_head_930_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_head_930_);
if (v_isSharedCheck_964_ == 0)
{
v___x_938_ = v_head_930_;
v_isShared_939_ = v_isSharedCheck_964_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_rhs_936_);
lean_inc(v_lhs_935_);
lean_dec(v_head_930_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_964_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; 
lean_inc_ref(v_rhs_936_);
lean_inc_ref(v_lhs_935_);
v___x_940_ = l_Lean_Meta_isExprDefEq(v_lhs_935_, v_rhs_936_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; uint8_t v___x_942_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = lean_unbox(v_a_941_);
lean_dec(v_a_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
lean_dec(v_tail_931_);
v___x_943_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1);
v___x_944_ = l_Lean_indentExpr(v_lhs_935_);
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 7);
lean_ctor_set(v___x_938_, 1, v___x_944_);
lean_ctor_set(v___x_938_, 0, v___x_943_);
v___x_946_ = v___x_938_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_944_);
v___x_946_ = v_reuseFailAlloc_954_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 7);
lean_ctor_set(v___x_933_, 1, v___x_947_);
lean_ctor_set(v___x_933_, 0, v___x_946_);
v___x_949_ = v___x_933_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_947_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = l_Lean_indentExpr(v_rhs_936_);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_951_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_952_;
}
}
}
else
{
lean_del_object(v___x_938_);
lean_dec_ref(v_rhs_936_);
lean_dec_ref(v_lhs_935_);
lean_del_object(v___x_933_);
v_as_922_ = v_tail_931_;
goto _start;
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_del_object(v___x_938_);
lean_dec_ref(v_rhs_936_);
lean_dec_ref(v_lhs_935_);
lean_del_object(v___x_933_);
lean_dec(v_tail_931_);
v_a_956_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_940_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_940_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___boxed(lean_object* v_as_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_as_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object* v_hint_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_pattern_982_; lean_object* v_constraints_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1025_; 
v_pattern_982_ = lean_ctor_get(v_hint_976_, 0);
v_constraints_983_ = lean_ctor_get(v_hint_976_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_hint_976_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_985_ = v_hint_976_;
v_isShared_986_ = v_isSharedCheck_1025_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_constraints_983_);
lean_inc(v_pattern_982_);
lean_dec(v_hint_976_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1025_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; 
v___x_987_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_constraints_983_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_lhs_988_; lean_object* v_rhs_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref_known(v___x_987_, 1);
v_lhs_988_ = lean_ctor_get(v_pattern_982_, 0);
v_rhs_989_ = lean_ctor_get(v_pattern_982_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_pattern_982_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_991_ = v_pattern_982_;
v_isShared_992_ = v_isSharedCheck_1024_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_rhs_989_);
lean_inc(v_lhs_988_);
lean_dec(v_pattern_982_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1024_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; 
lean_inc_ref(v_rhs_989_);
lean_inc_ref(v_lhs_988_);
v___x_993_ = l_Lean_Meta_isExprDefEq(v_lhs_988_, v_rhs_989_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1015_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1015_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1015_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; 
v___x_998_ = lean_unbox(v_a_994_);
lean_dec(v_a_994_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_del_object(v___x_996_);
v___x_999_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1);
v___x_1000_ = l_Lean_indentExpr(v_lhs_988_);
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 7);
lean_ctor_set(v___x_991_, 1, v___x_1000_);
lean_ctor_set(v___x_991_, 0, v___x_999_);
v___x_1002_ = v___x_991_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 7);
lean_ctor_set(v___x_985_, 1, v___x_1003_);
lean_ctor_set(v___x_985_, 0, v___x_1002_);
v___x_1005_ = v___x_985_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = l_Lean_indentExpr(v_rhs_989_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_1007_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
return v___x_1008_;
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_del_object(v___x_991_);
lean_dec_ref(v_rhs_989_);
lean_dec_ref(v_lhs_988_);
lean_del_object(v___x_985_);
v___x_1011_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1011_);
v___x_1013_ = v___x_996_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_del_object(v___x_991_);
lean_dec_ref(v_rhs_989_);
lean_dec_ref(v_lhs_988_);
lean_del_object(v___x_985_);
v_a_1016_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_993_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_993_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
else
{
lean_del_object(v___x_985_);
lean_dec_ref(v_pattern_982_);
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object* v_hint_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_hint_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object* v_00_u03b1_1033_, lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_msg_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(v_00_u03b1_1041_, v_msg_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(lean_object* v_k_1049_, uint8_t v_allowLevelAssignments_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1050_, v_k_1049_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_a_1065_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1056_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1056_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(lean_object* v_k_1073_, lean_object* v_allowLevelAssignments_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1080_; lean_object* v_res_1081_; 
v_allowLevelAssignments_boxed_1080_ = lean_unbox(v_allowLevelAssignments_1074_);
v_res_1081_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_1073_, v_allowLevelAssignments_boxed_1080_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(lean_object* v_00_u03b1_1082_, lean_object* v_k_1083_, uint8_t v_allowLevelAssignments_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_1083_, v_allowLevelAssignments_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(lean_object* v_00_u03b1_1091_, lean_object* v_k_1092_, lean_object* v_allowLevelAssignments_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1099_; lean_object* v_res_1100_; 
v_allowLevelAssignments_boxed_1099_ = lean_unbox(v_allowLevelAssignments_1093_);
v_res_1100_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(v_00_u03b1_1091_, v_k_1092_, v_allowLevelAssignments_boxed_1099_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1100_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg(){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__1);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___dummy_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg();
return v_res_1107_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg();
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_1117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
lean_ctor_set(v___x_1117_, 2, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1118_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__4, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__4);
v___x_1119_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3);
v___x_1120_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_1121_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
v___x_1122_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v___x_1120_);
lean_ctor_set(v___x_1122_, 2, v___x_1119_);
lean_ctor_set(v___x_1122_, 3, v___x_1120_);
lean_ctor_set(v___x_1122_, 4, v___x_1120_);
lean_ctor_set(v___x_1122_, 5, v___x_1120_);
lean_ctor_set(v___x_1122_, 6, v___x_1120_);
lean_ctor_set(v___x_1122_, 7, v___x_1118_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(lean_object* v_ext_1123_, lean_object* v_b_1124_, uint8_t v_kind_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_toCold_1130_; lean_object* v_currNamespace_1131_; lean_object* v___x_1132_; lean_object* v_env_1133_; lean_object* v_nextMacroScope_1134_; lean_object* v_ngen_1135_; lean_object* v_auxDeclNGen_1136_; lean_object* v_traceState_1137_; lean_object* v_recordedDeps_1138_; lean_object* v_messages_1139_; lean_object* v_infoState_1140_; lean_object* v_snapshotTasks_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1168_; 
v_toCold_1130_ = lean_ctor_get(v___y_1127_, 0);
v_currNamespace_1131_ = lean_ctor_get(v_toCold_1130_, 4);
v___x_1132_ = lean_st_ref_take(v___y_1128_);
v_env_1133_ = lean_ctor_get(v___x_1132_, 0);
v_nextMacroScope_1134_ = lean_ctor_get(v___x_1132_, 1);
v_ngen_1135_ = lean_ctor_get(v___x_1132_, 2);
v_auxDeclNGen_1136_ = lean_ctor_get(v___x_1132_, 3);
v_traceState_1137_ = lean_ctor_get(v___x_1132_, 4);
v_recordedDeps_1138_ = lean_ctor_get(v___x_1132_, 6);
v_messages_1139_ = lean_ctor_get(v___x_1132_, 7);
v_infoState_1140_ = lean_ctor_get(v___x_1132_, 8);
v_snapshotTasks_1141_ = lean_ctor_get(v___x_1132_, 9);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v___x_1132_, 5);
lean_dec(v_unused_1169_);
v___x_1143_ = v___x_1132_;
v_isShared_1144_ = v_isSharedCheck_1168_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snapshotTasks_1141_);
lean_inc(v_infoState_1140_);
lean_inc(v_messages_1139_);
lean_inc(v_recordedDeps_1138_);
lean_inc(v_traceState_1137_);
lean_inc(v_auxDeclNGen_1136_);
lean_inc(v_ngen_1135_);
lean_inc(v_nextMacroScope_1134_);
lean_inc(v_env_1133_);
lean_dec(v___x_1132_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1168_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_inc(v_currNamespace_1131_);
v___x_1145_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1133_, v_ext_1123_, v_b_1124_, v_kind_1125_, v_currNamespace_1131_);
v___x_1146_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 5, v___x_1146_);
lean_ctor_set(v___x_1143_, 0, v___x_1145_);
v___x_1148_ = v___x_1143_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_nextMacroScope_1134_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_ngen_1135_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_auxDeclNGen_1136_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_traceState_1137_);
lean_ctor_set(v_reuseFailAlloc_1167_, 5, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1167_, 6, v_recordedDeps_1138_);
lean_ctor_set(v_reuseFailAlloc_1167_, 7, v_messages_1139_);
lean_ctor_set(v_reuseFailAlloc_1167_, 8, v_infoState_1140_);
lean_ctor_set(v_reuseFailAlloc_1167_, 9, v_snapshotTasks_1141_);
v___x_1148_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_mctx_1151_; lean_object* v_zetaDeltaFVarIds_1152_; lean_object* v_postponed_1153_; lean_object* v_diag_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1165_; 
v___x_1149_ = lean_st_ref_put(v___y_1128_, v___x_1148_);
v___x_1150_ = lean_st_ref_take(v___y_1126_);
v_mctx_1151_ = lean_ctor_get(v___x_1150_, 0);
v_zetaDeltaFVarIds_1152_ = lean_ctor_get(v___x_1150_, 2);
v_postponed_1153_ = lean_ctor_get(v___x_1150_, 3);
v_diag_1154_ = lean_ctor_get(v___x_1150_, 4);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1150_, 1);
lean_dec(v_unused_1166_);
v___x_1156_ = v___x_1150_;
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_diag_1154_);
lean_inc(v_postponed_1153_);
lean_inc(v_zetaDeltaFVarIds_1152_);
lean_inc(v_mctx_1151_);
lean_dec(v___x_1150_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__5);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v___x_1159_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_mctx_1151_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_zetaDeltaFVarIds_1152_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_postponed_1153_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_diag_1154_);
v___x_1161_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_st_ref_put(v___y_1126_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1158_);
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(lean_object* v_ext_1170_, lean_object* v_b_1171_, lean_object* v_kind_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v_kind_boxed_1177_; lean_object* v_res_1178_; 
v_kind_boxed_1177_ = lean_unbox(v_kind_1172_);
v_res_1178_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_1170_, v_b_1171_, v_kind_boxed_1177_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(lean_object* v_ref_1179_, lean_object* v_msg_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_toCold_1186_; lean_object* v_currRecDepth_1187_; lean_object* v_ref_1188_; uint16_t v_optionFlags_1189_; uint8_t v_suppressElabErrors_1190_; uint8_t v_checkDeprecated_1191_; uint8_t v_isRecordingDeps_1192_; lean_object* v_ref_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_toCold_1186_ = lean_ctor_get(v___y_1183_, 0);
v_currRecDepth_1187_ = lean_ctor_get(v___y_1183_, 1);
v_ref_1188_ = lean_ctor_get(v___y_1183_, 2);
v_optionFlags_1189_ = lean_ctor_get_uint16(v___y_1183_, sizeof(void*)*3);
v_suppressElabErrors_1190_ = lean_ctor_get_uint8(v___y_1183_, sizeof(void*)*3 + 2);
v_checkDeprecated_1191_ = lean_ctor_get_uint8(v___y_1183_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1192_ = lean_ctor_get_uint8(v___y_1183_, sizeof(void*)*3 + 4);
v_ref_1193_ = l_Lean_replaceRef(v_ref_1179_, v_ref_1188_);
lean_inc(v_currRecDepth_1187_);
lean_inc_ref(v_toCold_1186_);
v___x_1194_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1194_, 0, v_toCold_1186_);
lean_ctor_set(v___x_1194_, 1, v_currRecDepth_1187_);
lean_ctor_set(v___x_1194_, 2, v_ref_1193_);
lean_ctor_set_uint16(v___x_1194_, sizeof(void*)*3, v_optionFlags_1189_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*3 + 2, v_suppressElabErrors_1190_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*3 + 3, v_checkDeprecated_1191_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*3 + 4, v_isRecordingDeps_1192_);
v___x_1195_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_1180_, v___y_1181_, v___y_1182_, v___x_1194_, v___y_1184_);
lean_dec_ref_known(v___x_1194_, 3);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_ref_1196_, lean_object* v_msg_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_ref_1196_, v_msg_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v_ref_1196_);
return v_res_1203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__0);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
lean_ctor_set(v___x_1208_, 2, v___x_1207_);
lean_ctor_set(v___x_1208_, 3, v___x_1207_);
lean_ctor_set(v___x_1208_, 4, v___x_1206_);
lean_ctor_set(v___x_1208_, 5, v___x_1206_);
lean_ctor_set(v___x_1208_, 6, v___x_1206_);
lean_ctor_set(v___x_1208_, 7, v___x_1206_);
lean_ctor_set(v___x_1208_, 8, v___x_1206_);
lean_ctor_set(v___x_1208_, 9, v___x_1206_);
lean_ctor_set(v___x_1208_, 10, v___x_1206_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(32u);
v___x_1210_ = lean_mk_empty_array_with_capacity(v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__3(void){
_start:
{
size_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = ((size_t)5ULL);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_unsigned_to_nat(32u);
v___x_1215_ = lean_mk_empty_array_with_capacity(v___x_1214_);
v___x_1216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2);
v___x_1217_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v___x_1215_);
lean_ctor_set(v___x_1217_, 2, v___x_1213_);
lean_ctor_set(v___x_1217_, 3, v___x_1213_);
lean_ctor_set_usize(v___x_1217_, 4, v___x_1212_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = lean_box(1);
v___x_1219_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__3);
v___x_1220_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__0);
v___x_1221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___x_1219_);
lean_ctor_set(v___x_1221_, 2, v___x_1218_);
return v___x_1221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__5));
v___x_1224_ = l_Lean_stringToMessageData(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__8(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__7));
v___x_1227_ = l_Lean_stringToMessageData(v___x_1226_);
return v___x_1227_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__10(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__9));
v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__12(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__11));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__14(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__13));
v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__15));
v___x_1239_ = l_Lean_stringToMessageData(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__17));
v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_msg_1243_, lean_object* v_declHint_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_env_1249_; uint8_t v___x_1250_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_st_ref_get(v___y_1245_);
v_env_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref(v_env_1249_);
lean_dec(v___x_1248_);
v___x_1250_ = l_Lean_Name_isAnonymous(v_declHint_1244_);
if (v___x_1250_ == 0)
{
uint8_t v_isExporting_1251_; 
v_isExporting_1251_ = lean_ctor_get_uint8(v_env_1249_, sizeof(void*)*13);
if (v_isExporting_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v_env_1249_);
lean_dec(v_declHint_1244_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_msg_1243_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
lean_inc_ref(v_env_1249_);
v___x_1253_ = l_Lean_Environment_setExporting(v_env_1249_, v___x_1250_);
lean_inc(v_declHint_1244_);
lean_inc_ref(v___x_1253_);
v___x_1254_ = l_Lean_Environment_contains(v___x_1253_, v_declHint_1244_, v_isExporting_1251_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v___x_1253_);
lean_dec_ref(v_env_1249_);
lean_dec(v_declHint_1244_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_msg_1243_);
return v___x_1255_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_c_1261_; lean_object* v___x_1262_; 
v___x_1256_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_1257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4);
v___x_1258_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1253_);
v___x_1259_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1253_);
lean_ctor_set(v___x_1259_, 1, v___x_1256_);
lean_ctor_set(v___x_1259_, 2, v___x_1257_);
lean_ctor_set(v___x_1259_, 3, v___x_1258_);
lean_inc(v_declHint_1244_);
v___x_1260_ = l_Lean_MessageData_ofConstName(v_declHint_1244_, v___x_1250_);
v_c_1261_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1261_, 0, v___x_1259_);
lean_ctor_set(v_c_1261_, 1, v___x_1260_);
v___x_1262_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1253_, v_declHint_1244_);
lean_dec_ref(v___x_1253_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v_env_1249_);
lean_dec(v_declHint_1244_);
v___x_1263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v_c_1261_);
v___x_1265_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__8);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_MessageData_note(v___x_1266_);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v_msg_1243_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
else
{
lean_object* v_val_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1304_; 
v_val_1270_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1272_ = v___x_1262_;
v_isShared_1273_ = v_isSharedCheck_1304_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_val_1270_);
lean_dec(v___x_1262_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1304_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v_moduleNames_1275_; lean_object* v_mod_1276_; uint8_t v___x_1277_; 
v___x_1274_ = l_Lean_Environment_header(v_env_1249_);
lean_dec_ref(v_env_1249_);
v_moduleNames_1275_ = lean_ctor_get(v___x_1274_, 4);
lean_inc_ref(v_moduleNames_1275_);
lean_dec_ref(v___x_1274_);
v_mod_1276_ = lean_array_get(v___x_1247_, v_moduleNames_1275_, v_val_1270_);
lean_dec(v_val_1270_);
lean_dec_ref(v_moduleNames_1275_);
v___x_1277_ = l_Lean_isPrivateName(v_declHint_1244_);
lean_dec(v_declHint_1244_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__10);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v_c_1261_);
v___x_1280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__12);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_MessageData_ofName(v_mod_1276_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__14);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Lean_MessageData_note(v___x_1285_);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v_msg_1243_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1287_);
v___x_1289_ = v___x_1272_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1291_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6);
v___x_1292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v_c_1261_);
v___x_1293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = l_Lean_MessageData_ofName(v_mod_1276_);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = l_Lean_MessageData_note(v___x_1298_);
v___x_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_msg_1243_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1300_);
v___x_1302_ = v___x_1272_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1305_; 
lean_dec_ref(v_env_1249_);
lean_dec(v_declHint_1244_);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_msg_1243_);
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1306_, lean_object* v_declHint_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg(v_msg_1306_, v_declHint_1307_, v___y_1308_);
lean_dec(v___y_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object* v_msg_1311_, lean_object* v_declHint_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1328_; 
v___x_1318_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg(v_msg_1311_, v_declHint_1312_, v___y_1316_);
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1328_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1328_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1323_ = l_Lean_unknownIdentifierMessageTag;
v___x_1324_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_a_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1324_);
v___x_1326_ = v___x_1321_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object* v_msg_1329_, lean_object* v_declHint_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7(v_msg_1329_, v_declHint_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1337_, lean_object* v_msg_1338_, lean_object* v_declHint_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v_a_1346_; lean_object* v___x_1347_; 
v___x_1345_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7(v_msg_1338_, v_declHint_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref(v___x_1345_);
v___x_1347_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_ref_1337_, v_a_1346_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1348_, lean_object* v_msg_1349_, lean_object* v_declHint_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1348_, v_msg_1349_, v_declHint_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v_ref_1348_);
return v_res_1356_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1363_, lean_object* v_constName_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1370_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1371_ = 0;
lean_inc(v_constName_1364_);
v___x_1372_ = l_Lean_MessageData_ofConstName(v_constName_1364_, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1370_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1363_, v___x_1375_, v_constName_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1377_, lean_object* v_constName_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg(v_ref_1377_, v_constName_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v_ref_1377_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(lean_object* v_constName_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_ref_1391_; lean_object* v___x_1392_; 
v_ref_1391_ = lean_ctor_get(v___y_1388_, 2);
v___x_1392_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg(v_ref_1391_, v_constName_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(lean_object* v_constName_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v_env_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1406_ = lean_st_ref_get(v___y_1404_);
v_env_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_env_1407_);
lean_dec(v___x_1406_);
v___x_1408_ = 0;
lean_inc(v_constName_1400_);
v___x_1409_ = l_Lean_Environment_find_x3f(v_env_1407_, v_constName_1400_, v___x_1408_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
return v___x_1410_;
}
else
{
lean_object* v_val_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_constName_1400_);
v_val_1411_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1409_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_val_1411_);
lean_dec(v___x_1409_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 0);
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_val_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(lean_object* v_constName_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_constName_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1425_;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_Meta_addUnificationHint___lam__0___closed__0));
v___x_1428_ = l_Lean_stringToMessageData(v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object* v_declName_1429_, uint8_t v_kind_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
lean_inc(v_declName_1429_);
v___x_1436_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_declName_1429_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1436_, 1);
v___x_1438_ = 0;
v___x_1439_ = l_Lean_ConstantInfo_value_x3f(v_a_1437_, v___x_1438_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec(v_declName_1429_);
v___x_1440_ = lean_obj_once(&l_Lean_Meta_addUnificationHint___lam__0___closed__1, &l_Lean_Meta_addUnificationHint___lam__0___closed__1_once, _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1);
v___x_1441_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_1440_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
return v___x_1441_;
}
else
{
lean_object* v_val_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_val_1442_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1443_ = lean_box(0);
v___x_1444_ = l_Lean_Meta_lambdaMetaTelescope(v_val_1442_, v___x_1443_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v_val_1442_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v_snd_1446_; lean_object* v_snd_1447_; lean_object* v___x_1448_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v_snd_1446_ = lean_ctor_get(v_a_1445_, 1);
lean_inc(v_snd_1446_);
lean_dec(v_a_1445_);
v_snd_1447_ = lean_ctor_get(v_snd_1446_, 1);
lean_inc(v_snd_1447_);
lean_dec(v_snd_1446_);
v___x_1448_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
lean_dec(v_declName_1429_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_a_1449_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
return v___x_1450_;
}
else
{
lean_object* v_a_1451_; lean_object* v_pattern_1452_; lean_object* v_lhs_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1488_; 
v_a_1451_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1448_, 1);
v_pattern_1452_ = lean_ctor_get(v_a_1451_, 0);
lean_inc_ref(v_pattern_1452_);
v_lhs_1453_ = lean_ctor_get(v_pattern_1452_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_pattern_1452_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_pattern_1452_, 1);
lean_dec(v_unused_1489_);
v___x_1455_ = v_pattern_1452_;
v_isShared_1456_ = v_isSharedCheck_1488_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_lhs_1453_);
lean_dec(v_pattern_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1488_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v_config_1458_; uint8_t v_trackZetaDelta_1459_; lean_object* v_zetaDeltaSet_1460_; lean_object* v_lctx_1461_; lean_object* v_localInstances_1462_; lean_object* v_defEqCtx_x3f_1463_; lean_object* v_synthPendingDepth_1464_; lean_object* v_customCanUnfoldPredicate_x3f_1465_; uint8_t v_univApprox_1466_; uint8_t v_inTypeClassResolution_1467_; uint8_t v_cacheInferType_1468_; uint64_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1457_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_1458_ = lean_ctor_get(v___x_1457_, 0);
v_trackZetaDelta_1459_ = lean_ctor_get_uint8(v___y_1431_, sizeof(void*)*7);
v_zetaDeltaSet_1460_ = lean_ctor_get(v___y_1431_, 1);
v_lctx_1461_ = lean_ctor_get(v___y_1431_, 2);
v_localInstances_1462_ = lean_ctor_get(v___y_1431_, 3);
v_defEqCtx_x3f_1463_ = lean_ctor_get(v___y_1431_, 4);
v_synthPendingDepth_1464_ = lean_ctor_get(v___y_1431_, 5);
v_customCanUnfoldPredicate_x3f_1465_ = lean_ctor_get(v___y_1431_, 6);
v_univApprox_1466_ = lean_ctor_get_uint8(v___y_1431_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1467_ = lean_ctor_get_uint8(v___y_1431_, sizeof(void*)*7 + 2);
v_cacheInferType_1468_ = lean_ctor_get_uint8(v___y_1431_, sizeof(void*)*7 + 3);
v___x_1469_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1458_);
lean_inc_ref(v_config_1458_);
v___x_1470_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1470_, 0, v_config_1458_);
lean_ctor_set_uint64(v___x_1470_, sizeof(void*)*1, v___x_1469_);
lean_inc(v_customCanUnfoldPredicate_x3f_1465_);
lean_inc(v_synthPendingDepth_1464_);
lean_inc(v_defEqCtx_x3f_1463_);
lean_inc_ref(v_localInstances_1462_);
lean_inc_ref(v_lctx_1461_);
lean_inc(v_zetaDeltaSet_1460_);
v___x_1471_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v_zetaDeltaSet_1460_);
lean_ctor_set(v___x_1471_, 2, v_lctx_1461_);
lean_ctor_set(v___x_1471_, 3, v_localInstances_1462_);
lean_ctor_set(v___x_1471_, 4, v_defEqCtx_x3f_1463_);
lean_ctor_set(v___x_1471_, 5, v_synthPendingDepth_1464_);
lean_ctor_set(v___x_1471_, 6, v_customCanUnfoldPredicate_x3f_1465_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*7, v_trackZetaDelta_1459_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*7 + 1, v_univApprox_1466_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1467_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*7 + 3, v_cacheInferType_1468_);
v___x_1472_ = l_Lean_Meta_DiscrTree_mkPath(v_lhs_1453_, v___x_1438_, v___x_1471_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec_ref_known(v___x_1471_, 7);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_a_1451_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_dec_ref_known(v___x_1474_, 1);
v___x_1475_ = l_Lean_Meta_unificationHintExtension;
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v_declName_1429_);
lean_ctor_set(v___x_1455_, 0, v_a_1473_);
v___x_1477_ = v___x_1455_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_declName_1429_);
v___x_1477_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v___x_1475_, v___x_1477_, v_kind_1430_, v___y_1432_, v___y_1433_, v___y_1434_);
return v___x_1478_;
}
}
else
{
lean_dec(v_a_1473_);
lean_del_object(v___x_1455_);
lean_dec(v_declName_1429_);
return v___x_1474_;
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_del_object(v___x_1455_);
lean_dec(v_a_1451_);
lean_dec(v_declName_1429_);
v_a_1480_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1472_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1472_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_declName_1429_);
v_a_1490_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1444_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1444_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_declName_1429_);
v_a_1498_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1436_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1436_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object* v_declName_1506_, lean_object* v_kind_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
uint8_t v_kind_boxed_1513_; lean_object* v_res_1514_; 
v_kind_boxed_1513_ = lean_unbox(v_kind_1507_);
v_res_1514_ = l_Lean_Meta_addUnificationHint___lam__0(v_declName_1506_, v_kind_boxed_1513_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* v_declName_1515_, uint8_t v_kind_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v___f_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; 
v___x_1522_ = lean_box(v_kind_1516_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1523_, 0, v_declName_1515_);
lean_closure_set(v___f_1523_, 1, v___x_1522_);
v___x_1524_ = 0;
v___x_1525_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v___f_1523_, v___x_1524_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* v_declName_1526_, lean_object* v_kind_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
uint8_t v_kind_boxed_1533_; lean_object* v_res_1534_; 
v_kind_boxed_1533_ = lean_unbox(v_kind_1527_);
v_res_1534_ = l_Lean_Meta_addUnificationHint(v_declName_1526_, v_kind_boxed_1533_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object* v_00_u03b1_1535_, lean_object* v_00_u03b2_1536_, lean_object* v_00_u03c3_1537_, lean_object* v_ext_1538_, lean_object* v_b_1539_, uint8_t v_kind_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_1538_, v_b_1539_, v_kind_1540_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object* v_00_u03b1_1547_, lean_object* v_00_u03b2_1548_, lean_object* v_00_u03c3_1549_, lean_object* v_ext_1550_, lean_object* v_b_1551_, lean_object* v_kind_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v_kind_boxed_1558_; lean_object* v_res_1559_; 
v_kind_boxed_1558_ = lean_unbox(v_kind_1552_);
v_res_1559_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(v_00_u03b1_1547_, v_00_u03b2_1548_, v_00_u03c3_1549_, v_ext_1550_, v_b_1551_, v_kind_boxed_1558_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object* v_00_u03b1_1560_, lean_object* v_constName_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1568_, lean_object* v_constName_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(v_00_u03b1_1568_, v_constName_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2___redArg(){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2___redArg___boxed(lean_object* v___dummy_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2___redArg();
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2(lean_object* v_00_u03b2_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1584_, lean_object* v_ref_1585_, lean_object* v_constName_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg(v_ref_1585_, v_constName_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_ref_1594_, lean_object* v_constName_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2(v_00_u03b1_1593_, v_ref_1594_, v_constName_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v_ref_1594_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_1602_, lean_object* v_ref_1603_, lean_object* v_msg_1604_, lean_object* v_declHint_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1603_, v_msg_1604_, v_declHint_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_ref_1613_, lean_object* v_msg_1614_, lean_object* v_declHint_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_1612_, v_ref_1613_, v_msg_1614_, v_declHint_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v_ref_1613_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8(lean_object* v_msg_1622_, lean_object* v_declHint_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg(v_msg_1622_, v_declHint_1623_, v___y_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_1630_, lean_object* v_declHint_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8(v_msg_1630_, v_declHint_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_00_u03b1_1638_, lean_object* v_ref_1639_, lean_object* v_msg_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_ref_1639_, v_msg_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b1_1647_, lean_object* v_ref_1648_, lean_object* v_msg_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8(v_00_u03b1_1647_, v_ref_1648_, v_msg_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v_ref_1648_);
return v_res_1655_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1662_; uint64_t v___x_1663_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1663_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1665_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set_uint64(v___x_1666_, sizeof(void*)*1, v___x_1664_);
return v___x_1666_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
return v___x_1670_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
lean_ctor_set(v___x_1672_, 2, v___x_1671_);
lean_ctor_set(v___x_1672_, 3, v___x_1671_);
lean_ctor_set(v___x_1672_, 4, v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1673_, lean_object* v___x_1674_, lean_object* v_declName_1675_, lean_object* v_stx_1676_, uint8_t v_kind_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1676_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1681_) == 0)
{
uint8_t v___x_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; size_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref_known(v___x_1681_, 1);
v___x_1682_ = 0;
v___x_1683_ = 1;
v___x_1684_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1685_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1686_ = lean_unsigned_to_nat(32u);
v___x_1687_ = lean_mk_empty_array_with_capacity(v___x_1686_);
v___x_1688_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2);
v___x_1689_ = ((size_t)5ULL);
lean_inc_n(v___x_1673_, 7);
v___x_1690_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1687_);
lean_ctor_set(v___x_1690_, 2, v___x_1673_);
lean_ctor_set(v___x_1690_, 3, v___x_1673_);
lean_ctor_set_usize(v___x_1690_, 4, v___x_1689_);
v___x_1691_ = lean_box(1);
lean_inc_ref(v___x_1690_);
v___x_1692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1685_);
lean_ctor_set(v___x_1692_, 1, v___x_1690_);
lean_ctor_set(v___x_1692_, 2, v___x_1691_);
v___x_1693_ = lean_mk_empty_array_with_capacity(v___x_1673_);
v___x_1694_ = lean_box(0);
lean_inc(v___x_1674_);
v___x_1695_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1695_, 0, v___x_1684_);
lean_ctor_set(v___x_1695_, 1, v___x_1674_);
lean_ctor_set(v___x_1695_, 2, v___x_1692_);
lean_ctor_set(v___x_1695_, 3, v___x_1693_);
lean_ctor_set(v___x_1695_, 4, v___x_1694_);
lean_ctor_set(v___x_1695_, 5, v___x_1673_);
lean_ctor_set(v___x_1695_, 6, v___x_1694_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*7, v___x_1682_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*7 + 1, v___x_1682_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*7 + 2, v___x_1682_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*7 + 3, v___x_1683_);
v___x_1696_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1673_);
lean_ctor_set(v___x_1696_, 1, v___x_1673_);
lean_ctor_set(v___x_1696_, 2, v___x_1673_);
lean_ctor_set(v___x_1696_, 3, v___x_1673_);
lean_ctor_set(v___x_1696_, 4, v___x_1685_);
lean_ctor_set(v___x_1696_, 5, v___x_1685_);
lean_ctor_set(v___x_1696_, 6, v___x_1685_);
lean_ctor_set(v___x_1696_, 7, v___x_1685_);
lean_ctor_set(v___x_1696_, 8, v___x_1685_);
lean_ctor_set(v___x_1696_, 9, v___x_1685_);
lean_ctor_set(v___x_1696_, 10, v___x_1685_);
v___x_1697_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
v___x_1698_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1685_);
lean_ctor_set(v___x_1699_, 1, v___x_1685_);
lean_ctor_set(v___x_1699_, 2, v___x_1673_);
v___x_1700_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1697_);
lean_ctor_set(v___x_1700_, 1, v___x_1685_);
lean_ctor_set(v___x_1700_, 2, v___x_1698_);
lean_ctor_set(v___x_1700_, 3, v___x_1685_);
lean_ctor_set(v___x_1700_, 4, v___x_1685_);
lean_ctor_set(v___x_1700_, 5, v___x_1685_);
lean_ctor_set(v___x_1700_, 6, v___x_1685_);
lean_ctor_set(v___x_1700_, 7, v___x_1699_);
v___x_1701_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1696_);
lean_ctor_set(v___x_1702_, 1, v___x_1700_);
lean_ctor_set(v___x_1702_, 2, v___x_1674_);
lean_ctor_set(v___x_1702_, 3, v___x_1690_);
lean_ctor_set(v___x_1702_, 4, v___x_1701_);
v___x_1703_ = lean_box(0);
v___x_1704_ = lean_st_mk_ref(v___x_1702_);
v___x_1705_ = l_Lean_Meta_addUnificationHint(v_declName_1675_, v_kind_1677_, v___x_1695_, v___x_1704_, v___y_1678_, v___y_1679_);
lean_dec_ref_known(v___x_1695_, 7);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; 
v_unused_1714_ = lean_ctor_get(v___x_1705_, 0);
lean_dec(v_unused_1714_);
v___x_1707_ = v___x_1705_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_dec(v___x_1705_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = lean_st_ref_get(v___x_1704_);
lean_dec(v___x_1704_);
lean_dec(v___x_1709_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1703_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1703_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
lean_dec(v___x_1704_);
return v___x_1705_;
}
}
else
{
lean_dec(v_declName_1675_);
lean_dec(v___x_1674_);
lean_dec(v___x_1673_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v_declName_1717_, lean_object* v_stx_1718_, lean_object* v_kind_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v_kind_boxed_1723_; lean_object* v_res_1724_; 
v_kind_boxed_1723_ = lean_unbox(v_kind_1719_);
v_res_1724_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1715_, v___x_1716_, v_declName_1717_, v_stx_1718_, v_kind_boxed_1723_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v_toCold_1730_; lean_object* v_env_1731_; lean_object* v_options_1732_; uint8_t v___x_1733_; lean_object* v_env_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1729_ = lean_st_ref_get(v___y_1727_);
v_toCold_1730_ = lean_ctor_get(v___y_1726_, 0);
v_env_1731_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_ref(v_env_1731_);
lean_dec(v___x_1729_);
v_options_1732_ = lean_ctor_get(v_toCold_1730_, 2);
v___x_1733_ = 0;
v_env_1734_ = l_Lean_Environment_setRecordingDeps(v_env_1731_, v___x_1733_);
v___x_1735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_1736_ = lean_unsigned_to_nat(32u);
v___x_1737_ = lean_mk_empty_array_with_capacity(v___x_1736_);
lean_dec_ref(v___x_1737_);
v___x_1738_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4);
lean_inc_ref(v_options_1732_);
v___x_1739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1739_, 0, v_env_1734_);
lean_ctor_set(v___x_1739_, 1, v___x_1735_);
lean_ctor_set(v___x_1739_, 2, v___x_1738_);
lean_ctor_set(v___x_1739_, 3, v_options_1732_);
v___x_1740_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v_msgData_1725_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_ref_1751_; lean_object* v___x_1752_; lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1761_; 
v_ref_1751_ = lean_ctor_get(v___y_1748_, 2);
v___x_1752_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msg_1747_, v___y_1748_, v___y_1749_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
lean_inc(v_ref_1751_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_ref_1751_);
lean_ctor_set(v___x_1757_, 1, v_a_1753_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 1);
lean_ctor_set(v___x_1755_, 0, v___x_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
return v_res_1766_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1773_, lean_object* v_decl_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1778_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1779_ = l_Lean_MessageData_ofName(v___x_1773_);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v___x_1782_, v___y_1775_, v___y_1776_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1784_, lean_object* v_decl_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1784_, v_decl_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v_decl_1785_);
return v_res_1789_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = lean_unsigned_to_nat(3033092106u);
v___x_1834_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1835_ = l_Lean_Name_num___override(v___x_1834_, v___x_1833_);
return v___x_1835_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1838_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1839_ = l_Lean_Name_str___override(v___x_1838_, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1842_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1843_ = l_Lean_Name_str___override(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_unsigned_to_nat(2u);
v___x_1845_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1846_ = l_Lean_Name_num___override(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1853_ = 0;
v___x_1854_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1855_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1856_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1857_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v___x_1855_);
lean_ctor_set(v___x_1857_, 2, v___x_1854_);
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*3, v___x_1853_);
return v___x_1857_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1858_; lean_object* v___f_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___f_1858_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___f_1859_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1860_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___f_1859_);
lean_ctor_set(v___x_1861_, 2, v___f_1858_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1864_ = l_Lean_registerBuiltinAttribute(v___x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v_a_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1867_, lean_object* v_msg_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1868_, v___y_1869_, v___y_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1873_, lean_object* v_msg_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(v_00_u03b1_1873_, v_msg_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints(lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v_ext_1883_; lean_object* v_toEnvExtension_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1882_ = l_Lean_Meta_unificationHintExtension;
v_ext_1883_ = lean_ctor_get(v___x_1882_, 1);
v_toEnvExtension_1884_ = lean_ctor_get(v_ext_1883_, 0);
v___x_1885_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
lean_inc_ref(v_toEnvExtension_1884_);
v___x_1886_ = l_Lean_recordExtGenAccess___redArg(v_toEnvExtension_1884_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1898_; 
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v___x_1886_, 0);
lean_dec(v_unused_1899_);
v___x_1888_ = v___x_1886_;
v_isShared_1889_ = v_isSharedCheck_1898_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v___x_1886_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1898_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v_env_1891_; lean_object* v_asyncMode_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1890_ = lean_st_ref_get(v_a_1880_);
v_env_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc_ref(v_env_1891_);
lean_dec(v___x_1890_);
v_asyncMode_1892_ = lean_ctor_get(v_toEnvExtension_1884_, 2);
v___x_1893_ = 1;
v___x_1894_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1885_, v___x_1882_, v_env_1891_, v_asyncMode_1892_, v___x_1893_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1894_);
v___x_1896_ = v___x_1888_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_a_1900_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1886_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1886_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints___boxed(lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints(v_a_1908_, v_a_1909_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* v_p_1912_, lean_object* v_e_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___y_1920_; lean_object* v___x_1937_; uint8_t v_transparency_1938_; uint8_t v___x_1939_; uint8_t v___x_1940_; 
v___x_1937_ = l_Lean_Meta_Context_config(v_a_1914_);
v_transparency_1938_ = lean_ctor_get_uint8(v___x_1937_, 9);
lean_dec_ref(v___x_1937_);
v___x_1939_ = 2;
v___x_1940_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v_keyedConfig_1941_; uint8_t v_trackZetaDelta_1942_; lean_object* v_zetaDeltaSet_1943_; lean_object* v_lctx_1944_; lean_object* v_localInstances_1945_; lean_object* v_defEqCtx_x3f_1946_; lean_object* v_synthPendingDepth_1947_; lean_object* v_customCanUnfoldPredicate_x3f_1948_; uint8_t v_univApprox_1949_; uint8_t v_inTypeClassResolution_1950_; uint8_t v_cacheInferType_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_keyedConfig_1941_ = lean_ctor_get(v_a_1914_, 0);
v_trackZetaDelta_1942_ = lean_ctor_get_uint8(v_a_1914_, sizeof(void*)*7);
v_zetaDeltaSet_1943_ = lean_ctor_get(v_a_1914_, 1);
v_lctx_1944_ = lean_ctor_get(v_a_1914_, 2);
v_localInstances_1945_ = lean_ctor_get(v_a_1914_, 3);
v_defEqCtx_x3f_1946_ = lean_ctor_get(v_a_1914_, 4);
v_synthPendingDepth_1947_ = lean_ctor_get(v_a_1914_, 5);
v_customCanUnfoldPredicate_x3f_1948_ = lean_ctor_get(v_a_1914_, 6);
v_univApprox_1949_ = lean_ctor_get_uint8(v_a_1914_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1950_ = lean_ctor_get_uint8(v_a_1914_, sizeof(void*)*7 + 2);
v_cacheInferType_1951_ = lean_ctor_get_uint8(v_a_1914_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1941_);
v___x_1952_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1939_, v_keyedConfig_1941_);
lean_inc(v_customCanUnfoldPredicate_x3f_1948_);
lean_inc(v_synthPendingDepth_1947_);
lean_inc(v_defEqCtx_x3f_1946_);
lean_inc_ref(v_localInstances_1945_);
lean_inc_ref(v_lctx_1944_);
lean_inc(v_zetaDeltaSet_1943_);
v___x_1953_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
lean_ctor_set(v___x_1953_, 1, v_zetaDeltaSet_1943_);
lean_ctor_set(v___x_1953_, 2, v_lctx_1944_);
lean_ctor_set(v___x_1953_, 3, v_localInstances_1945_);
lean_ctor_set(v___x_1953_, 4, v_defEqCtx_x3f_1946_);
lean_ctor_set(v___x_1953_, 5, v_synthPendingDepth_1947_);
lean_ctor_set(v___x_1953_, 6, v_customCanUnfoldPredicate_x3f_1948_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*7, v_trackZetaDelta_1942_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*7 + 1, v_univApprox_1949_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1950_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*7 + 3, v_cacheInferType_1951_);
lean_inc(v_a_1917_);
lean_inc_ref(v_a_1916_);
lean_inc(v_a_1915_);
v___x_1954_ = lean_is_expr_def_eq(v_p_1912_, v_e_1913_, v___x_1953_, v_a_1915_, v_a_1916_, v_a_1917_);
v___y_1920_ = v___x_1954_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1955_; 
lean_inc(v_a_1917_);
lean_inc_ref(v_a_1916_);
lean_inc(v_a_1915_);
lean_inc_ref(v_a_1914_);
v___x_1955_ = lean_is_expr_def_eq(v_p_1912_, v_e_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
v___y_1920_ = v___x_1955_;
goto v___jp_1919_;
}
v___jp_1919_:
{
if (lean_obj_tag(v___y_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_a_1921_ = lean_ctor_get(v___y_1920_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___y_1920_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___y_1920_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___y_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_a_1929_ = lean_ctor_get(v___y_1920_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___y_1920_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___y_1920_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___y_1920_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object* v_p_1956_, lean_object* v_e_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_p_1956_, v_e_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object* v_x_1964_, lean_object* v_x_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
if (lean_obj_tag(v_x_1964_) == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = l_List_reverse___redArg(v_x_1965_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
else
{
lean_object* v_tail_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1991_; 
v_tail_1973_ = lean_ctor_get(v_x_1964_, 1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_x_1964_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v_x_1964_, 0);
lean_dec(v_unused_1992_);
v___x_1975_ = v_x_1964_;
v_isShared_1976_ = v_isSharedCheck_1991_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_tail_1973_);
lean_dec(v_x_1964_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1991_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v_x_1965_);
lean_ctor_set(v___x_1975_, 0, v_a_1978_);
v___x_1980_ = v___x_1975_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1978_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_x_1965_);
v___x_1980_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
v_x_1964_ = v_tail_1973_;
v_x_1965_ = v___x_1980_;
goto _start;
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_del_object(v___x_1975_);
lean_dec(v_tail_1973_);
lean_dec(v_x_1965_);
v_a_1983_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1977_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1977_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v_x_1993_, v_x_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
return v_res_2000_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2001_; double v___x_2002_; 
v___x_2001_ = lean_unsigned_to_nat(0u);
v___x_2002_ = lean_float_of_nat(v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object* v_cls_2006_, lean_object* v_msg_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_ref_2013_; lean_object* v___x_2014_; lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2060_; 
v_ref_2013_ = lean_ctor_get(v___y_2010_, 2);
v___x_2014_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2060_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2060_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v_traceState_2020_; lean_object* v_env_2021_; lean_object* v_nextMacroScope_2022_; lean_object* v_ngen_2023_; lean_object* v_auxDeclNGen_2024_; lean_object* v_cache_2025_; lean_object* v_recordedDeps_2026_; lean_object* v_messages_2027_; lean_object* v_infoState_2028_; lean_object* v_snapshotTasks_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2059_; 
v___x_2019_ = lean_st_ref_take(v___y_2011_);
v_traceState_2020_ = lean_ctor_get(v___x_2019_, 4);
v_env_2021_ = lean_ctor_get(v___x_2019_, 0);
v_nextMacroScope_2022_ = lean_ctor_get(v___x_2019_, 1);
v_ngen_2023_ = lean_ctor_get(v___x_2019_, 2);
v_auxDeclNGen_2024_ = lean_ctor_get(v___x_2019_, 3);
v_cache_2025_ = lean_ctor_get(v___x_2019_, 5);
v_recordedDeps_2026_ = lean_ctor_get(v___x_2019_, 6);
v_messages_2027_ = lean_ctor_get(v___x_2019_, 7);
v_infoState_2028_ = lean_ctor_get(v___x_2019_, 8);
v_snapshotTasks_2029_ = lean_ctor_get(v___x_2019_, 9);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2031_ = v___x_2019_;
v_isShared_2032_ = v_isSharedCheck_2059_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_snapshotTasks_2029_);
lean_inc(v_infoState_2028_);
lean_inc(v_messages_2027_);
lean_inc(v_recordedDeps_2026_);
lean_inc(v_cache_2025_);
lean_inc(v_traceState_2020_);
lean_inc(v_auxDeclNGen_2024_);
lean_inc(v_ngen_2023_);
lean_inc(v_nextMacroScope_2022_);
lean_inc(v_env_2021_);
lean_dec(v___x_2019_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2059_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
uint64_t v_tid_2033_; lean_object* v_traces_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2058_; 
v_tid_2033_ = lean_ctor_get_uint64(v_traceState_2020_, sizeof(void*)*1);
v_traces_2034_ = lean_ctor_get(v_traceState_2020_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_traceState_2020_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2036_ = v_traceState_2020_;
v_isShared_2037_ = v_isSharedCheck_2058_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_traces_2034_);
lean_dec(v_traceState_2020_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2058_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; double v___x_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
v___x_2041_ = 0;
v___x_2042_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_2043_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2043_, 0, v_cls_2006_);
lean_ctor_set(v___x_2043_, 1, v___x_2039_);
lean_ctor_set(v___x_2043_, 2, v___x_2042_);
lean_ctor_set_float(v___x_2043_, sizeof(void*)*3, v___x_2040_);
lean_ctor_set_float(v___x_2043_, sizeof(void*)*3 + 8, v___x_2040_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*3 + 16, v___x_2041_);
v___x_2044_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2));
v___x_2045_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set(v___x_2045_, 1, v_a_2015_);
lean_ctor_set(v___x_2045_, 2, v___x_2044_);
lean_inc(v_ref_2013_);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_ref_2013_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l_Lean_PersistentArray_push___redArg(v_traces_2034_, v___x_2046_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2047_);
v___x_2049_ = v___x_2036_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2047_);
lean_ctor_set_uint64(v_reuseFailAlloc_2057_, sizeof(void*)*1, v_tid_2033_);
v___x_2049_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 4, v___x_2049_);
v___x_2051_ = v___x_2031_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_env_2021_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_nextMacroScope_2022_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_ngen_2023_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_auxDeclNGen_2024_);
lean_ctor_set(v_reuseFailAlloc_2056_, 4, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2056_, 5, v_cache_2025_);
lean_ctor_set(v_reuseFailAlloc_2056_, 6, v_recordedDeps_2026_);
lean_ctor_set(v_reuseFailAlloc_2056_, 7, v_messages_2027_);
lean_ctor_set(v_reuseFailAlloc_2056_, 8, v_infoState_2028_);
lean_ctor_set(v_reuseFailAlloc_2056_, 9, v_snapshotTasks_2029_);
v___x_2051_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = lean_st_ref_put(v___y_2011_, v___x_2051_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2038_);
v___x_2054_ = v___x_2017_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2038_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object* v_cls_2061_, lean_object* v_msg_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2061_, v_msg_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object* v_as_2072_, size_t v_sz_2073_, size_t v_i_2074_, lean_object* v_b_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_a_2082_; uint8_t v___x_2086_; 
v___x_2086_ = lean_usize_dec_lt(v_i_2074_, v_sz_2073_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_b_2075_);
return v___x_2087_;
}
else
{
lean_object* v_snd_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2178_; 
v_snd_2088_ = lean_ctor_get(v_b_2075_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_b_2075_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; 
v_unused_2179_ = lean_ctor_get(v_b_2075_, 0);
lean_dec(v_unused_2179_);
v___x_2090_ = v_b_2075_;
v_isShared_2091_ = v_isSharedCheck_2178_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_snd_2088_);
lean_dec(v_b_2075_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2178_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_array_2092_; lean_object* v_start_2093_; lean_object* v_stop_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v_array_2092_ = lean_ctor_get(v_snd_2088_, 0);
v_start_2093_ = lean_ctor_get(v_snd_2088_, 1);
v_stop_2094_ = lean_ctor_get(v_snd_2088_, 2);
v___x_2095_ = lean_box(0);
v___x_2096_ = lean_nat_dec_lt(v_start_2093_, v_stop_2094_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2098_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2095_);
v___x_2098_ = v___x_2090_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_snd_2088_);
v___x_2098_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; 
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
else
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2174_; 
lean_inc(v_stop_2094_);
lean_inc(v_start_2093_);
lean_inc_ref(v_array_2092_);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_snd_2088_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; lean_object* v_unused_2176_; lean_object* v_unused_2177_; 
v_unused_2175_ = lean_ctor_get(v_snd_2088_, 2);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_snd_2088_, 1);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_snd_2088_, 0);
lean_dec(v_unused_2177_);
v___x_2102_ = v_snd_2088_;
v_isShared_2103_ = v_isSharedCheck_2174_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v_snd_2088_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2174_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2104_ = lean_array_fget(v_array_2092_, v_start_2093_);
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_nat_add(v_start_2093_, v___x_2105_);
lean_dec(v_start_2093_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 1, v___x_2106_);
v___x_2108_ = v___x_2102_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_array_2092_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_stop_2094_);
v___x_2108_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
uint8_t v___x_2109_; uint8_t v___x_2110_; uint8_t v___x_2111_; 
v___x_2109_ = 3;
v___x_2110_ = lean_unbox(v___x_2104_);
lean_dec(v___x_2104_);
v___x_2111_ = l_Lean_instBEqBinderInfo_beq(v___x_2110_, v___x_2109_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2113_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2108_);
lean_ctor_set(v___x_2090_, 0, v___x_2095_);
v___x_2113_ = v___x_2090_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v___x_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
v_a_2082_ = v___x_2113_;
goto v___jp_2081_;
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_array_uget_borrowed(v_as_2072_, v_i_2074_);
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2076_);
lean_inc(v_a_2115_);
v___x_2116_ = lean_infer_type(v_a_2115_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = l_Lean_Meta_trySynthInstance(v_a_2117_, v___x_2095_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2156_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2156_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2156_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
if (lean_obj_tag(v_a_2119_) == 1)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
lean_del_object(v___x_2121_);
v_a_2123_ = lean_ctor_get(v_a_2119_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v_a_2119_, 1);
lean_inc(v_a_2115_);
v___x_2124_ = l_Lean_Meta_isExprDefEq(v_a_2115_, v_a_2123_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2140_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2140_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2140_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
uint8_t v___x_2129_; 
v___x_2129_ = lean_unbox(v_a_2125_);
lean_dec(v_a_2125_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2108_);
lean_ctor_set(v___x_2090_, 0, v___x_2130_);
v___x_2132_ = v___x_2090_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2108_);
v___x_2132_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2132_);
v___x_2134_ = v___x_2127_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
else
{
lean_object* v___x_2138_; 
lean_del_object(v___x_2127_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2108_);
lean_ctor_set(v___x_2090_, 0, v___x_2095_);
v___x_2138_ = v___x_2090_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2108_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
v_a_2082_ = v___x_2138_;
goto v___jp_2081_;
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v___x_2108_);
lean_del_object(v___x_2090_);
v_a_2141_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2124_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2124_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
lean_dec(v_a_2119_);
v___x_2149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2108_);
lean_ctor_set(v___x_2090_, 0, v___x_2149_);
v___x_2151_ = v___x_2090_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2108_);
v___x_2151_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2153_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2151_);
v___x_2153_ = v___x_2121_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v___x_2108_);
lean_del_object(v___x_2090_);
v_a_2157_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2118_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2118_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v___x_2108_);
lean_del_object(v___x_2090_);
v_a_2165_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2116_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2116_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
}
}
}
}
v___jp_2081_:
{
size_t v___x_2083_; size_t v___x_2084_; 
v___x_2083_ = ((size_t)1ULL);
v___x_2084_ = lean_usize_add(v_i_2074_, v___x_2083_);
v_i_2074_ = v___x_2084_;
v_b_2075_ = v_a_2082_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object* v_as_2180_, lean_object* v_sz_2181_, lean_object* v_i_2182_, lean_object* v_b_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
size_t v_sz_boxed_2189_; size_t v_i_boxed_2190_; lean_object* v_res_2191_; 
v_sz_boxed_2189_ = lean_unbox_usize(v_sz_2181_);
lean_dec(v_sz_2181_);
v_i_boxed_2190_ = lean_unbox_usize(v_i_2182_);
lean_dec(v_i_2182_);
v_res_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_as_2180_, v_sz_boxed_2189_, v_i_boxed_2190_, v_b_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_as_2180_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object* v_as_x27_2198_, lean_object* v_b_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
if (lean_obj_tag(v_as_x27_2198_) == 0)
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v_b_2199_);
return v___x_2205_;
}
else
{
lean_object* v_head_2206_; lean_object* v_tail_2207_; lean_object* v_lhs_2208_; lean_object* v_rhs_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec_ref(v_b_2199_);
v_head_2206_ = lean_ctor_get(v_as_x27_2198_, 0);
v_tail_2207_ = lean_ctor_get(v_as_x27_2198_, 1);
v_lhs_2208_ = lean_ctor_get(v_head_2206_, 0);
v_rhs_2209_ = lean_ctor_get(v_head_2206_, 1);
v___x_2210_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
lean_inc(v___y_2203_);
lean_inc_ref(v___y_2202_);
lean_inc(v___y_2201_);
lean_inc_ref(v___y_2200_);
lean_inc_ref(v_rhs_2209_);
lean_inc_ref(v_lhs_2208_);
v___x_2211_ = lean_is_expr_def_eq(v_lhs_2208_, v_rhs_2209_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2222_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2222_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2222_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
uint8_t v___x_2216_; 
v___x_2216_ = lean_unbox(v_a_2212_);
lean_dec(v_a_2212_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2217_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__1));
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2217_);
v___x_2219_ = v___x_2214_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
else
{
lean_del_object(v___x_2214_);
v_as_x27_2198_ = v_tail_2207_;
v_b_2199_ = v___x_2210_;
goto _start;
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
v_a_2223_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2211_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2211_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object* v_as_x27_2231_, lean_object* v_b_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2231_, v_b_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v_as_x27_2231_);
return v_res_2238_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7(void){
_start:
{
lean_object* v_cls_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_cls_2253_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2254_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6));
v___x_2255_ = l_Lean_Name_append(v___x_2254_, v_cls_2253_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8));
v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object* v_candidate_2259_, lean_object* v_t_2260_, lean_object* v_s_2261_, uint8_t v_mayPostpone_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v_cls_2268_; lean_object* v___x_2269_; 
v_cls_2268_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2269_ = l_Lean_Meta_saveState___redArg(v_a_2264_, v_a_2266_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2522_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2522_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2522_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_a_2275_; uint8_t v_a_2302_; lean_object* v___x_2314_; lean_object* v_cache_2315_; lean_object* v_mctx_2316_; lean_object* v_zetaDeltaFVarIds_2317_; lean_object* v_postponed_2318_; lean_object* v_diag_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2521_; 
v___x_2314_ = lean_st_ref_take(v_a_2264_);
v_cache_2315_ = lean_ctor_get(v___x_2314_, 1);
v_mctx_2316_ = lean_ctor_get(v___x_2314_, 0);
v_zetaDeltaFVarIds_2317_ = lean_ctor_get(v___x_2314_, 2);
v_postponed_2318_ = lean_ctor_get(v___x_2314_, 3);
v_diag_2319_ = lean_ctor_get(v___x_2314_, 4);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2321_ = v___x_2314_;
v_isShared_2322_ = v_isSharedCheck_2521_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_diag_2319_);
lean_inc(v_postponed_2318_);
lean_inc(v_zetaDeltaFVarIds_2317_);
lean_inc(v_cache_2315_);
lean_inc(v_mctx_2316_);
lean_dec(v___x_2314_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2521_;
goto v_resetjp_2320_;
}
v___jp_2274_:
{
uint8_t v___x_2276_; 
v___x_2276_ = l_Lean_Exception_isInterrupt(v_a_2275_);
if (v___x_2276_ == 0)
{
uint8_t v___x_2277_; 
lean_inc_ref(v_a_2275_);
v___x_2277_ = l_Lean_Exception_isRuntime(v_a_2275_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; 
lean_del_object(v___x_2272_);
v___x_2278_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2270_, v_a_2264_, v_a_2266_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; 
v_unused_2286_ = lean_ctor_get(v___x_2278_, 0);
lean_dec(v_unused_2286_);
v___x_2280_ = v___x_2278_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_dec(v___x_2278_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set_tag(v___x_2280_, 1);
lean_ctor_set(v___x_2280_, 0, v_a_2275_);
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2275_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v_a_2275_);
v_a_2287_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2278_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2278_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_object* v___x_2296_; 
lean_dec(v_a_2270_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set_tag(v___x_2272_, 1);
lean_ctor_set(v___x_2272_, 0, v_a_2275_);
v___x_2296_ = v___x_2272_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2275_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
lean_object* v___x_2299_; 
lean_dec(v_a_2270_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set_tag(v___x_2272_, 1);
lean_ctor_set(v___x_2272_, 0, v_a_2275_);
v___x_2299_ = v___x_2272_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2275_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
v___jp_2301_:
{
lean_object* v___x_2303_; 
lean_inc(v_a_2270_);
v___x_2303_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2270_, v_a_2264_, v_a_2266_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2311_; 
lean_del_object(v___x_2272_);
lean_dec(v_a_2270_);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; 
v_unused_2312_ = lean_ctor_get(v___x_2303_, 0);
lean_dec(v_unused_2312_);
v___x_2305_ = v___x_2303_;
v_isShared_2306_ = v_isSharedCheck_2311_;
goto v_resetjp_2304_;
}
else
{
lean_dec(v___x_2303_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2311_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2307_ = lean_box(v_a_2302_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2307_);
v___x_2309_ = v___x_2305_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
else
{
lean_object* v_a_2313_; 
v_a_2313_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2303_, 1);
v_a_2275_ = v_a_2313_;
goto v___jp_2274_;
}
}
v_resetjp_2320_:
{
lean_object* v_inferType_2323_; lean_object* v_funInfo_2324_; lean_object* v_synthInstance_2325_; lean_object* v_whnf_2326_; lean_object* v_defEqPerm_2327_; lean_object* v_isUnitLike_2328_; lean_object* v_unfold_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2519_; 
v_inferType_2323_ = lean_ctor_get(v_cache_2315_, 0);
v_funInfo_2324_ = lean_ctor_get(v_cache_2315_, 1);
v_synthInstance_2325_ = lean_ctor_get(v_cache_2315_, 2);
v_whnf_2326_ = lean_ctor_get(v_cache_2315_, 3);
v_defEqPerm_2327_ = lean_ctor_get(v_cache_2315_, 5);
v_isUnitLike_2328_ = lean_ctor_get(v_cache_2315_, 6);
v_unfold_2329_ = lean_ctor_get(v_cache_2315_, 7);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_cache_2315_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v_cache_2315_, 4);
lean_dec(v_unused_2520_);
v___x_2331_ = v_cache_2315_;
v_isShared_2332_ = v_isSharedCheck_2519_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_unfold_2329_);
lean_inc(v_isUnitLike_2328_);
lean_inc(v_defEqPerm_2327_);
lean_inc(v_whnf_2326_);
lean_inc(v_synthInstance_2325_);
lean_inc(v_funInfo_2324_);
lean_inc(v_inferType_2323_);
lean_dec(v_cache_2315_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2519_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 4, v___x_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_inferType_2323_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_funInfo_2324_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_synthInstance_2325_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_whnf_2326_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2518_, 5, v_defEqPerm_2327_);
lean_ctor_set(v_reuseFailAlloc_2518_, 6, v_isUnitLike_2328_);
lean_ctor_set(v_reuseFailAlloc_2518_, 7, v_unfold_2329_);
v___x_2335_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 1, v___x_2335_);
v___x_2337_ = v___x_2321_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_mctx_2316_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_zetaDeltaFVarIds_2317_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_postponed_2318_);
lean_ctor_set(v_reuseFailAlloc_2517_, 4, v_diag_2319_);
v___x_2337_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_st_ref_put(v_a_2264_, v___x_2337_);
v___x_2339_ = l_Lean_Meta_getResetPostponed___redArg(v_a_2264_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; uint8_t v_a_2342_; uint8_t v_a_2385_; lean_object* v___x_2386_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
lean_inc(v_candidate_2259_);
v___x_2386_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_candidate_2259_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2388_ = l_Lean_ConstantInfo_levelParams(v_a_2387_);
v___x_2389_ = lean_box(0);
v___x_2390_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v___x_2388_, v___x_2389_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = 0;
v___x_2393_ = l_Lean_Core_instantiateValueLevelParams(v_a_2387_, v_a_2391_, v___x_2392_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2387_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = lean_box(0);
v___x_2396_ = l_Lean_Meta_lambdaMetaTelescope(v_a_2394_, v___x_2395_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2394_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v_snd_2398_; lean_object* v_fst_2399_; lean_object* v_fst_2400_; lean_object* v_snd_2401_; lean_object* v___x_2402_; uint8_t v_foApprox_2403_; uint8_t v_ctxApprox_2404_; uint8_t v_quasiPatternApprox_2405_; uint8_t v_constApprox_2406_; uint8_t v_isDefEqStuckEx_2407_; uint8_t v_proofIrrelevance_2408_; uint8_t v_assignSyntheticOpaque_2409_; uint8_t v_offsetCnstrs_2410_; uint8_t v_transparency_2411_; uint8_t v_etaStruct_2412_; uint8_t v_univApprox_2413_; uint8_t v_iota_2414_; uint8_t v_beta_2415_; uint8_t v_proj_2416_; uint8_t v_zeta_2417_; uint8_t v_zetaDelta_2418_; uint8_t v_zetaUnused_2419_; uint8_t v_zetaHave_2420_; uint8_t v_canUnfoldPredicateConfig_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2504_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v_snd_2398_ = lean_ctor_get(v_a_2397_, 1);
lean_inc(v_snd_2398_);
v_fst_2399_ = lean_ctor_get(v_a_2397_, 0);
lean_inc(v_fst_2399_);
lean_dec(v_a_2397_);
v_fst_2400_ = lean_ctor_get(v_snd_2398_, 0);
lean_inc(v_fst_2400_);
v_snd_2401_ = lean_ctor_get(v_snd_2398_, 1);
lean_inc(v_snd_2401_);
lean_dec(v_snd_2398_);
v___x_2402_ = l_Lean_Meta_Context_config(v_a_2263_);
v_foApprox_2403_ = lean_ctor_get_uint8(v___x_2402_, 0);
v_ctxApprox_2404_ = lean_ctor_get_uint8(v___x_2402_, 1);
v_quasiPatternApprox_2405_ = lean_ctor_get_uint8(v___x_2402_, 2);
v_constApprox_2406_ = lean_ctor_get_uint8(v___x_2402_, 3);
v_isDefEqStuckEx_2407_ = lean_ctor_get_uint8(v___x_2402_, 4);
v_proofIrrelevance_2408_ = lean_ctor_get_uint8(v___x_2402_, 6);
v_assignSyntheticOpaque_2409_ = lean_ctor_get_uint8(v___x_2402_, 7);
v_offsetCnstrs_2410_ = lean_ctor_get_uint8(v___x_2402_, 8);
v_transparency_2411_ = lean_ctor_get_uint8(v___x_2402_, 9);
v_etaStruct_2412_ = lean_ctor_get_uint8(v___x_2402_, 10);
v_univApprox_2413_ = lean_ctor_get_uint8(v___x_2402_, 11);
v_iota_2414_ = lean_ctor_get_uint8(v___x_2402_, 12);
v_beta_2415_ = lean_ctor_get_uint8(v___x_2402_, 13);
v_proj_2416_ = lean_ctor_get_uint8(v___x_2402_, 14);
v_zeta_2417_ = lean_ctor_get_uint8(v___x_2402_, 15);
v_zetaDelta_2418_ = lean_ctor_get_uint8(v___x_2402_, 16);
v_zetaUnused_2419_ = lean_ctor_get_uint8(v___x_2402_, 17);
v_zetaHave_2420_ = lean_ctor_get_uint8(v___x_2402_, 18);
v_canUnfoldPredicateConfig_2421_ = lean_ctor_get_uint8(v___x_2402_, 19);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2423_ = v___x_2402_;
v_isShared_2424_ = v_isSharedCheck_2504_;
goto v_resetjp_2422_;
}
else
{
lean_dec(v___x_2402_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2504_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; 
v___x_2425_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_2401_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_dec_ref_known(v___x_2425_, 1);
lean_del_object(v___x_2423_);
lean_dec(v_fst_2400_);
lean_dec(v_fst_2399_);
lean_dec(v_a_2340_);
lean_dec_ref(v_s_2261_);
lean_dec_ref(v_t_2260_);
lean_dec(v_candidate_2259_);
v_a_2302_ = v___x_2392_;
goto v___jp_2301_;
}
else
{
lean_object* v_a_2426_; lean_object* v_pattern_2427_; uint8_t v_trackZetaDelta_2428_; lean_object* v_zetaDeltaSet_2429_; lean_object* v_lctx_2430_; lean_object* v_localInstances_2431_; lean_object* v_defEqCtx_x3f_2432_; lean_object* v_synthPendingDepth_2433_; lean_object* v_customCanUnfoldPredicate_x3f_2434_; uint8_t v_univApprox_2435_; uint8_t v_inTypeClassResolution_2436_; uint8_t v_cacheInferType_2437_; lean_object* v_constraints_2438_; lean_object* v_lhs_2439_; lean_object* v_rhs_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2503_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v_pattern_2427_ = lean_ctor_get(v_a_2426_, 0);
lean_inc_ref(v_pattern_2427_);
v_trackZetaDelta_2428_ = lean_ctor_get_uint8(v_a_2263_, sizeof(void*)*7);
v_zetaDeltaSet_2429_ = lean_ctor_get(v_a_2263_, 1);
v_lctx_2430_ = lean_ctor_get(v_a_2263_, 2);
v_localInstances_2431_ = lean_ctor_get(v_a_2263_, 3);
v_defEqCtx_x3f_2432_ = lean_ctor_get(v_a_2263_, 4);
v_synthPendingDepth_2433_ = lean_ctor_get(v_a_2263_, 5);
v_customCanUnfoldPredicate_x3f_2434_ = lean_ctor_get(v_a_2263_, 6);
v_univApprox_2435_ = lean_ctor_get_uint8(v_a_2263_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2436_ = lean_ctor_get_uint8(v_a_2263_, sizeof(void*)*7 + 2);
v_cacheInferType_2437_ = lean_ctor_get_uint8(v_a_2263_, sizeof(void*)*7 + 3);
v_constraints_2438_ = lean_ctor_get(v_a_2426_, 1);
lean_inc(v_constraints_2438_);
lean_dec(v_a_2426_);
v_lhs_2439_ = lean_ctor_get(v_pattern_2427_, 0);
v_rhs_2440_ = lean_ctor_get(v_pattern_2427_, 1);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_pattern_2427_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2442_ = v_pattern_2427_;
v_isShared_2443_ = v_isSharedCheck_2503_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_rhs_2440_);
lean_inc(v_lhs_2439_);
lean_dec(v_pattern_2427_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2503_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2424_ == 0)
{
v___x_2445_ = v___x_2423_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 0, v_foApprox_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 1, v_ctxApprox_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 2, v_quasiPatternApprox_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 3, v_constApprox_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 4, v_isDefEqStuckEx_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 6, v_proofIrrelevance_2408_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 7, v_assignSyntheticOpaque_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 8, v_offsetCnstrs_2410_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 9, v_transparency_2411_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 10, v_etaStruct_2412_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 11, v_univApprox_2413_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 12, v_iota_2414_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 13, v_beta_2415_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 14, v_proj_2416_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 15, v_zeta_2417_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 16, v_zetaDelta_2418_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 17, v_zetaUnused_2419_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 18, v_zetaHave_2420_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, 19, v_canUnfoldPredicateConfig_2421_);
v___x_2445_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
uint64_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_ctor_set_uint8(v___x_2445_, 5, v___x_2392_);
v___x_2446_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2445_);
v___x_2447_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set_uint64(v___x_2447_, sizeof(void*)*1, v___x_2446_);
lean_inc(v_customCanUnfoldPredicate_x3f_2434_);
lean_inc(v_synthPendingDepth_2433_);
lean_inc(v_defEqCtx_x3f_2432_);
lean_inc_ref(v_localInstances_2431_);
lean_inc_ref(v_lctx_2430_);
lean_inc(v_zetaDeltaSet_2429_);
v___x_2448_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v_zetaDeltaSet_2429_);
lean_ctor_set(v___x_2448_, 2, v_lctx_2430_);
lean_ctor_set(v___x_2448_, 3, v_localInstances_2431_);
lean_ctor_set(v___x_2448_, 4, v_defEqCtx_x3f_2432_);
lean_ctor_set(v___x_2448_, 5, v_synthPendingDepth_2433_);
lean_ctor_set(v___x_2448_, 6, v_customCanUnfoldPredicate_x3f_2434_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*7, v_trackZetaDelta_2428_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*7 + 1, v_univApprox_2435_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2436_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*7 + 3, v_cacheInferType_2437_);
v___x_2449_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_lhs_2439_, v_t_2260_, v___x_2448_, v_a_2264_, v_a_2265_, v_a_2266_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; uint8_t v___x_2451_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___x_2451_ = lean_unbox(v_a_2450_);
lean_dec(v_a_2450_);
if (v___x_2451_ == 0)
{
lean_dec_ref_known(v___x_2448_, 7);
lean_del_object(v___x_2442_);
lean_dec_ref(v_rhs_2440_);
lean_dec(v_constraints_2438_);
lean_dec(v_fst_2400_);
lean_dec(v_fst_2399_);
lean_dec(v_a_2340_);
lean_dec_ref(v_s_2261_);
lean_dec(v_candidate_2259_);
v_a_2302_ = v___x_2392_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2452_; 
v___x_2452_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_rhs_2440_, v_s_2261_, v___x_2448_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec_ref_known(v___x_2448_, 7);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; uint8_t v___x_2486_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v___x_2486_ = lean_unbox(v_a_2453_);
if (v___x_2486_ == 0)
{
lean_dec(v_a_2453_);
lean_del_object(v___x_2442_);
lean_dec(v_constraints_2438_);
lean_dec(v_fst_2400_);
lean_dec(v_fst_2399_);
lean_dec(v_a_2340_);
lean_dec(v_candidate_2259_);
v_a_2302_ = v___x_2392_;
goto v___jp_2301_;
}
else
{
lean_object* v_toCold_2487_; lean_object* v_options_2488_; uint8_t v_hasTrace_2489_; 
v_toCold_2487_ = lean_ctor_get(v_a_2265_, 0);
v_options_2488_ = lean_ctor_get(v_toCold_2487_, 2);
v_hasTrace_2489_ = lean_ctor_get_uint8(v_options_2488_, sizeof(void*)*1);
if (v_hasTrace_2489_ == 0)
{
lean_del_object(v___x_2442_);
lean_dec(v_candidate_2259_);
v___y_2455_ = v_a_2263_;
v___y_2456_ = v_a_2264_;
v___y_2457_ = v_a_2265_;
v___y_2458_ = v_a_2266_;
goto v___jp_2454_;
}
else
{
lean_object* v_inheritedTraceOptions_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v_inheritedTraceOptions_2490_ = lean_ctor_get(v_toCold_2487_, 11);
v___x_2491_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7);
v___x_2492_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2490_, v_options_2488_, v___x_2491_);
if (v___x_2492_ == 0)
{
lean_del_object(v___x_2442_);
lean_dec(v_candidate_2259_);
v___y_2455_ = v_a_2263_;
v___y_2456_ = v_a_2264_;
v___y_2457_ = v_a_2265_;
v___y_2458_ = v_a_2266_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2493_ = l_Lean_MessageData_ofName(v_candidate_2259_);
v___x_2494_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9);
if (v_isShared_2443_ == 0)
{
lean_ctor_set_tag(v___x_2442_, 7);
lean_ctor_set(v___x_2442_, 1, v___x_2494_);
lean_ctor_set(v___x_2442_, 0, v___x_2493_);
v___x_2496_ = v___x_2442_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2268_, v___x_2496_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_dec_ref_known(v___x_2497_, 1);
v___y_2455_ = v_a_2263_;
v___y_2456_ = v_a_2264_;
v___y_2457_ = v_a_2265_;
v___y_2458_ = v_a_2266_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2498_; 
lean_dec(v_a_2453_);
lean_dec(v_constraints_2438_);
lean_dec(v_fst_2400_);
lean_dec(v_fst_2399_);
lean_dec(v_a_2340_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v_a_2275_ = v_a_2498_;
goto v___jp_2274_;
}
}
}
}
}
v___jp_2454_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4));
v___x_2460_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_constraints_2438_, v___x_2459_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v_constraints_2438_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v_fst_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2483_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2460_, 1);
v_fst_2462_ = lean_ctor_get(v_a_2461_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_a_2461_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v_a_2461_, 1);
lean_dec(v_unused_2484_);
v___x_2464_ = v_a_2461_;
v_isShared_2465_ = v_isSharedCheck_2483_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_fst_2462_);
lean_dec(v_a_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2483_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
if (lean_obj_tag(v_fst_2462_) == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = lean_array_get_size(v_fst_2400_);
v___x_2468_ = l_Array_toSubarray___redArg(v_fst_2400_, v___x_2466_, v___x_2467_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 1, v___x_2468_);
lean_ctor_set(v___x_2464_, 0, v___x_2395_);
v___x_2470_ = v___x_2464_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
size_t v_sz_2471_; size_t v___x_2472_; lean_object* v___x_2473_; 
v_sz_2471_ = lean_array_size(v_fst_2399_);
v___x_2472_ = ((size_t)0ULL);
v___x_2473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_fst_2399_, v_sz_2471_, v___x_2472_, v___x_2470_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v_fst_2399_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v_fst_2475_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v_fst_2475_ = lean_ctor_get(v_a_2474_, 0);
lean_inc(v_fst_2475_);
lean_dec(v_a_2474_);
if (lean_obj_tag(v_fst_2475_) == 0)
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_unbox(v_a_2453_);
lean_dec(v_a_2453_);
v_a_2342_ = v___x_2476_;
goto v___jp_2341_;
}
else
{
lean_object* v_val_2477_; uint8_t v___x_2478_; 
lean_dec(v_a_2453_);
v_val_2477_ = lean_ctor_get(v_fst_2475_, 0);
lean_inc(v_val_2477_);
lean_dec_ref_known(v_fst_2475_, 1);
v___x_2478_ = lean_unbox(v_val_2477_);
lean_dec(v_val_2477_);
v_a_2385_ = v___x_2478_;
goto v___jp_2384_;
}
}
else
{
lean_object* v_a_2479_; 
lean_dec(v_a_2453_);
lean_dec(v_a_2340_);
v_a_2479_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2473_, 1);
v_a_2275_ = v_a_2479_;
goto v___jp_2274_;
}
}
}
else
{
lean_object* v_val_2481_; uint8_t v___x_2482_; 
lean_del_object(v___x_2464_);
lean_dec(v_a_2453_);
lean_dec(v_fst_2400_);
lean_dec(v_fst_2399_);
v_val_2481_ = lean_ctor_get(v_fst_2462_, 0);
lean_inc(v_val_2481_);
lean_dec_ref_known(v_fst_2462_, 1);
v___x_2482_ = lean_unbox(v_val_2481_);
lean_dec(v_val_2481_);
v_a_2385_ = v___x_2482_;
goto v___jp_2384_;
}
}
}
else
{
lean_object* v_a_2485_; 
lean_dec(v_a_2453_);
lean_dec(v_fst_2400_);
lean_dec(v_fst_2399_);
lean_dec(v_a_2340_);
v_a_2485_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___x_2460_, 1);
v_a_2275_ = v_a_2485_;
goto v___jp_2274_;
}
}
}
else
{
lean_object* v_a_2500_; 
lean_del_object(v___x_2442_);
lean_dec(v_constraints_2438_);
lean_dec(v_fst_2400_);
lean_dec(v_fst_2399_);
lean_dec(v_a_2340_);
lean_dec(v_candidate_2259_);
v_a_2500_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2452_, 1);
v_a_2275_ = v_a_2500_;
goto v___jp_2274_;
}
}
}
else
{
lean_object* v_a_2501_; 
lean_dec_ref_known(v___x_2448_, 7);
lean_del_object(v___x_2442_);
lean_dec_ref(v_rhs_2440_);
lean_dec(v_constraints_2438_);
lean_dec(v_fst_2400_);
lean_dec(v_fst_2399_);
lean_dec(v_a_2340_);
lean_dec_ref(v_s_2261_);
lean_dec(v_candidate_2259_);
v_a_2501_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2449_, 1);
v_a_2275_ = v_a_2501_;
goto v___jp_2274_;
}
}
}
}
}
}
else
{
lean_object* v_a_2505_; 
lean_dec(v_a_2340_);
lean_dec_ref(v_s_2261_);
lean_dec_ref(v_t_2260_);
lean_dec(v_candidate_2259_);
v_a_2505_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2396_, 1);
v_a_2275_ = v_a_2505_;
goto v___jp_2274_;
}
}
else
{
lean_object* v_a_2506_; 
lean_dec(v_a_2340_);
lean_dec_ref(v_s_2261_);
lean_dec_ref(v_t_2260_);
lean_dec(v_candidate_2259_);
v_a_2506_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2393_, 1);
v_a_2275_ = v_a_2506_;
goto v___jp_2274_;
}
}
else
{
lean_object* v_a_2507_; 
lean_dec(v_a_2387_);
lean_dec(v_a_2340_);
lean_dec_ref(v_s_2261_);
lean_dec_ref(v_t_2260_);
lean_dec(v_candidate_2259_);
v_a_2507_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2390_, 1);
v_a_2275_ = v_a_2507_;
goto v___jp_2274_;
}
}
else
{
lean_object* v_a_2508_; 
lean_dec(v_a_2340_);
lean_dec_ref(v_s_2261_);
lean_dec_ref(v_t_2260_);
lean_dec(v_candidate_2259_);
v_a_2508_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2386_, 1);
v_a_2275_ = v_a_2508_;
goto v___jp_2274_;
}
v___jp_2341_:
{
uint8_t v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = 0;
v___x_2344_ = l_Lean_Meta_processPostponed(v_mayPostpone_2262_, v___x_2343_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2382_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2382_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2382_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_unbox(v_a_2345_);
lean_dec(v_a_2345_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_del_object(v___x_2347_);
lean_dec(v_a_2340_);
lean_inc(v_a_2270_);
v___x_2350_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2270_, v_a_2264_, v_a_2266_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2358_; 
lean_del_object(v___x_2272_);
lean_dec(v_a_2270_);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2350_, 0);
lean_dec(v_unused_2359_);
v___x_2352_ = v___x_2350_;
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
else
{
lean_dec(v___x_2350_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = lean_box(v___x_2343_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2354_);
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
lean_object* v_a_2360_; 
v_a_2360_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2350_, 1);
v_a_2275_ = v_a_2360_;
goto v___jp_2274_;
}
}
else
{
lean_object* v___x_2361_; lean_object* v_postponed_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v_mctx_2365_; lean_object* v_cache_2366_; lean_object* v_zetaDeltaFVarIds_2367_; lean_object* v_diag_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2380_; 
lean_del_object(v___x_2272_);
lean_dec(v_a_2270_);
v___x_2361_ = lean_st_ref_get(v_a_2264_);
v_postponed_2362_ = lean_ctor_get(v___x_2361_, 3);
lean_inc_ref(v_postponed_2362_);
lean_dec(v___x_2361_);
v___x_2363_ = l_Lean_PersistentArray_append___redArg(v_a_2340_, v_postponed_2362_);
lean_dec_ref(v_postponed_2362_);
v___x_2364_ = lean_st_ref_take(v_a_2264_);
v_mctx_2365_ = lean_ctor_get(v___x_2364_, 0);
v_cache_2366_ = lean_ctor_get(v___x_2364_, 1);
v_zetaDeltaFVarIds_2367_ = lean_ctor_get(v___x_2364_, 2);
v_diag_2368_ = lean_ctor_get(v___x_2364_, 4);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; 
v_unused_2381_ = lean_ctor_get(v___x_2364_, 3);
lean_dec(v_unused_2381_);
v___x_2370_ = v___x_2364_;
v_isShared_2371_ = v_isSharedCheck_2380_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_diag_2368_);
lean_inc(v_zetaDeltaFVarIds_2367_);
lean_inc(v_cache_2366_);
lean_inc(v_mctx_2365_);
lean_dec(v___x_2364_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2380_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 3, v___x_2363_);
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_mctx_2365_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_cache_2366_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_zetaDeltaFVarIds_2367_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v_diag_2368_);
v___x_2373_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2374_ = lean_st_ref_put(v_a_2264_, v___x_2373_);
v___x_2375_ = lean_box(v_a_2342_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2375_);
v___x_2377_ = v___x_2347_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
}
else
{
lean_object* v_a_2383_; 
lean_dec(v_a_2340_);
v_a_2383_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2344_, 1);
v_a_2275_ = v_a_2383_;
goto v___jp_2274_;
}
}
v___jp_2384_:
{
if (v_a_2385_ == 0)
{
lean_dec(v_a_2340_);
v_a_2302_ = v_a_2385_;
goto v___jp_2301_;
}
else
{
v_a_2342_ = v_a_2385_;
goto v___jp_2341_;
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_del_object(v___x_2272_);
lean_dec(v_a_2270_);
lean_dec_ref(v_s_2261_);
lean_dec_ref(v_t_2260_);
lean_dec(v_candidate_2259_);
v_a_2509_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2339_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2339_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
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
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec_ref(v_s_2261_);
lean_dec_ref(v_t_2260_);
lean_dec(v_candidate_2259_);
v_a_2523_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2269_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2269_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object* v_candidate_2531_, lean_object* v_t_2532_, lean_object* v_s_2533_, lean_object* v_mayPostpone_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
uint8_t v_mayPostpone_boxed_2540_; lean_object* v_res_2541_; 
v_mayPostpone_boxed_2540_ = lean_unbox(v_mayPostpone_2534_);
v_res_2541_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2531_, v_t_2532_, v_s_2533_, v_mayPostpone_boxed_2540_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
return v_res_2541_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_unsigned_to_nat(32u);
v___x_2543_ = lean_mk_empty_array_with_capacity(v___x_2542_);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2545_ = ((size_t)5ULL);
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = lean_unsigned_to_nat(32u);
v___x_2548_ = lean_mk_empty_array_with_capacity(v___x_2547_);
v___x_2549_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0);
v___x_2550_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2548_);
lean_ctor_set(v___x_2550_, 2, v___x_2546_);
lean_ctor_set(v___x_2550_, 3, v___x_2546_);
lean_ctor_set_usize(v___x_2550_, 4, v___x_2545_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; lean_object* v_traceState_2554_; lean_object* v_traces_2555_; lean_object* v___x_2556_; lean_object* v_traceState_2557_; lean_object* v_env_2558_; lean_object* v_nextMacroScope_2559_; lean_object* v_ngen_2560_; lean_object* v_auxDeclNGen_2561_; lean_object* v_cache_2562_; lean_object* v_recordedDeps_2563_; lean_object* v_messages_2564_; lean_object* v_infoState_2565_; lean_object* v_snapshotTasks_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2585_; 
v___x_2553_ = lean_st_ref_get(v___y_2551_);
v_traceState_2554_ = lean_ctor_get(v___x_2553_, 4);
lean_inc_ref(v_traceState_2554_);
lean_dec(v___x_2553_);
v_traces_2555_ = lean_ctor_get(v_traceState_2554_, 0);
lean_inc_ref(v_traces_2555_);
lean_dec_ref(v_traceState_2554_);
v___x_2556_ = lean_st_ref_take(v___y_2551_);
v_traceState_2557_ = lean_ctor_get(v___x_2556_, 4);
v_env_2558_ = lean_ctor_get(v___x_2556_, 0);
v_nextMacroScope_2559_ = lean_ctor_get(v___x_2556_, 1);
v_ngen_2560_ = lean_ctor_get(v___x_2556_, 2);
v_auxDeclNGen_2561_ = lean_ctor_get(v___x_2556_, 3);
v_cache_2562_ = lean_ctor_get(v___x_2556_, 5);
v_recordedDeps_2563_ = lean_ctor_get(v___x_2556_, 6);
v_messages_2564_ = lean_ctor_get(v___x_2556_, 7);
v_infoState_2565_ = lean_ctor_get(v___x_2556_, 8);
v_snapshotTasks_2566_ = lean_ctor_get(v___x_2556_, 9);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2568_ = v___x_2556_;
v_isShared_2569_ = v_isSharedCheck_2585_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_snapshotTasks_2566_);
lean_inc(v_infoState_2565_);
lean_inc(v_messages_2564_);
lean_inc(v_recordedDeps_2563_);
lean_inc(v_cache_2562_);
lean_inc(v_traceState_2557_);
lean_inc(v_auxDeclNGen_2561_);
lean_inc(v_ngen_2560_);
lean_inc(v_nextMacroScope_2559_);
lean_inc(v_env_2558_);
lean_dec(v___x_2556_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2585_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
uint64_t v_tid_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2583_; 
v_tid_2570_ = lean_ctor_get_uint64(v_traceState_2557_, sizeof(void*)*1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_traceState_2557_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; 
v_unused_2584_ = lean_ctor_get(v_traceState_2557_, 0);
lean_dec(v_unused_2584_);
v___x_2572_ = v_traceState_2557_;
v_isShared_2573_ = v_isSharedCheck_2583_;
goto v_resetjp_2571_;
}
else
{
lean_dec(v_traceState_2557_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2583_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2574_);
v___x_2576_ = v___x_2572_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2574_);
lean_ctor_set_uint64(v_reuseFailAlloc_2582_, sizeof(void*)*1, v_tid_2570_);
v___x_2576_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 4, v___x_2576_);
v___x_2578_ = v___x_2568_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_env_2558_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_nextMacroScope_2559_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_ngen_2560_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_auxDeclNGen_2561_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2581_, 5, v_cache_2562_);
lean_ctor_set(v_reuseFailAlloc_2581_, 6, v_recordedDeps_2563_);
lean_ctor_set(v_reuseFailAlloc_2581_, 7, v_messages_2564_);
lean_ctor_set(v_reuseFailAlloc_2581_, 8, v_infoState_2565_);
lean_ctor_set(v_reuseFailAlloc_2581_, 9, v_snapshotTasks_2566_);
v___x_2578_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = lean_st_ref_put(v___y_2551_, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_traces_2555_);
return v___x_2580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___boxed(lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2586_);
lean_dec(v___y_2586_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
return v_res_2600_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object* v_opts_2601_, lean_object* v_opt_2602_){
_start:
{
lean_object* v_name_2603_; lean_object* v_defValue_2604_; lean_object* v_map_2605_; lean_object* v___x_2606_; 
v_name_2603_ = lean_ctor_get(v_opt_2602_, 0);
v_defValue_2604_ = lean_ctor_get(v_opt_2602_, 1);
v_map_2605_ = lean_ctor_get(v_opts_2601_, 0);
v___x_2606_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2605_, v_name_2603_);
if (lean_obj_tag(v___x_2606_) == 0)
{
uint8_t v___x_2607_; 
v___x_2607_ = lean_unbox(v_defValue_2604_);
return v___x_2607_;
}
else
{
lean_object* v_val_2608_; 
v_val_2608_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_val_2608_);
lean_dec_ref_known(v___x_2606_, 1);
if (lean_obj_tag(v_val_2608_) == 1)
{
uint8_t v_v_2609_; 
v_v_2609_ = lean_ctor_get_uint8(v_val_2608_, 0);
lean_dec_ref_known(v_val_2608_, 0);
return v_v_2609_;
}
else
{
uint8_t v___x_2610_; 
lean_dec(v_val_2608_);
v___x_2610_ = lean_unbox(v_defValue_2604_);
return v___x_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object* v_opts_2611_, lean_object* v_opt_2612_){
_start:
{
uint8_t v_res_2613_; lean_object* v_r_2614_; 
v_res_2613_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2611_, v_opt_2612_);
lean_dec_ref(v_opt_2612_);
lean_dec_ref(v_opts_2611_);
v_r_2614_ = lean_box(v_res_2613_);
return v_r_2614_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0));
v___x_2617_ = l_Lean_stringToMessageData(v___x_2616_);
return v___x_2617_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2));
v___x_2620_ = l_Lean_stringToMessageData(v___x_2619_);
return v___x_2620_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4));
v___x_2623_ = l_Lean_stringToMessageData(v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object* v_candidate_2624_, lean_object* v_t_2625_, lean_object* v_s_2626_, lean_object* v_x_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2633_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1);
v___x_2634_ = l_Lean_MessageData_ofName(v_candidate_2624_);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = l_Lean_MessageData_ofExpr(v_t_2625_);
v___x_2639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2637_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
v___x_2640_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2639_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = l_Lean_MessageData_ofExpr(v_s_2626_);
v___x_2643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2641_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object* v_candidate_2645_, lean_object* v_t_2646_, lean_object* v_s_2647_, lean_object* v_x_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(v_candidate_2645_, v_t_2646_, v_s_2647_, v_x_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v_x_2648_);
return v_res_2654_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(lean_object* v_e_2655_){
_start:
{
if (lean_obj_tag(v_e_2655_) == 0)
{
uint8_t v___x_2656_; 
v___x_2656_ = 2;
return v___x_2656_;
}
else
{
lean_object* v_a_2657_; uint8_t v___x_2658_; 
v_a_2657_ = lean_ctor_get(v_e_2655_, 0);
v___x_2658_ = lean_unbox(v_a_2657_);
if (v___x_2658_ == 0)
{
uint8_t v___x_2659_; 
v___x_2659_ = 1;
return v___x_2659_;
}
else
{
uint8_t v___x_2660_; 
v___x_2660_ = 0;
return v___x_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(lean_object* v_e_2661_){
_start:
{
uint8_t v_res_2662_; lean_object* v_r_2663_; 
v_res_2662_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_e_2661_);
lean_dec_ref(v_e_2661_);
v_r_2663_ = lean_box(v_res_2662_);
return v_r_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(size_t v_sz_2664_, size_t v_i_2665_, lean_object* v_bs_2666_){
_start:
{
uint8_t v___x_2667_; 
v___x_2667_ = lean_usize_dec_lt(v_i_2665_, v_sz_2664_);
if (v___x_2667_ == 0)
{
return v_bs_2666_;
}
else
{
lean_object* v_v_2668_; lean_object* v_msg_2669_; lean_object* v___x_2670_; lean_object* v_bs_x27_2671_; size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v_v_2668_ = lean_array_uget_borrowed(v_bs_2666_, v_i_2665_);
v_msg_2669_ = lean_ctor_get(v_v_2668_, 1);
lean_inc_ref(v_msg_2669_);
v___x_2670_ = lean_unsigned_to_nat(0u);
v_bs_x27_2671_ = lean_array_uset(v_bs_2666_, v_i_2665_, v___x_2670_);
v___x_2672_ = ((size_t)1ULL);
v___x_2673_ = lean_usize_add(v_i_2665_, v___x_2672_);
v___x_2674_ = lean_array_uset(v_bs_x27_2671_, v_i_2665_, v_msg_2669_);
v_i_2665_ = v___x_2673_;
v_bs_2666_ = v___x_2674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8___boxed(lean_object* v_sz_2676_, lean_object* v_i_2677_, lean_object* v_bs_2678_){
_start:
{
size_t v_sz_boxed_2679_; size_t v_i_boxed_2680_; lean_object* v_res_2681_; 
v_sz_boxed_2679_ = lean_unbox_usize(v_sz_2676_);
lean_dec(v_sz_2676_);
v_i_boxed_2680_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_res_2681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(v_sz_boxed_2679_, v_i_boxed_2680_, v_bs_2678_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(lean_object* v_oldTraces_2682_, lean_object* v_data_2683_, lean_object* v_ref_2684_, lean_object* v_msg_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_toCold_2691_; lean_object* v_currRecDepth_2692_; lean_object* v_ref_2693_; uint16_t v_optionFlags_2694_; uint8_t v_suppressElabErrors_2695_; uint8_t v_checkDeprecated_2696_; uint8_t v_isRecordingDeps_2697_; lean_object* v_ref_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v_traceState_2701_; lean_object* v_traces_2702_; lean_object* v___x_2703_; size_t v_sz_2704_; size_t v___x_2705_; lean_object* v___x_2706_; lean_object* v_msg_2707_; lean_object* v___x_2708_; lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2747_; 
v_toCold_2691_ = lean_ctor_get(v___y_2688_, 0);
v_currRecDepth_2692_ = lean_ctor_get(v___y_2688_, 1);
v_ref_2693_ = lean_ctor_get(v___y_2688_, 2);
v_optionFlags_2694_ = lean_ctor_get_uint16(v___y_2688_, sizeof(void*)*3);
v_suppressElabErrors_2695_ = lean_ctor_get_uint8(v___y_2688_, sizeof(void*)*3 + 2);
v_checkDeprecated_2696_ = lean_ctor_get_uint8(v___y_2688_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2697_ = lean_ctor_get_uint8(v___y_2688_, sizeof(void*)*3 + 4);
v_ref_2698_ = l_Lean_replaceRef(v_ref_2684_, v_ref_2693_);
lean_inc(v_currRecDepth_2692_);
lean_inc_ref(v_toCold_2691_);
v___x_2699_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2699_, 0, v_toCold_2691_);
lean_ctor_set(v___x_2699_, 1, v_currRecDepth_2692_);
lean_ctor_set(v___x_2699_, 2, v_ref_2698_);
lean_ctor_set_uint16(v___x_2699_, sizeof(void*)*3, v_optionFlags_2694_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*3 + 2, v_suppressElabErrors_2695_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*3 + 3, v_checkDeprecated_2696_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*3 + 4, v_isRecordingDeps_2697_);
v___x_2700_ = lean_st_ref_get(v___y_2689_);
v_traceState_2701_ = lean_ctor_get(v___x_2700_, 4);
lean_inc_ref(v_traceState_2701_);
lean_dec(v___x_2700_);
v_traces_2702_ = lean_ctor_get(v_traceState_2701_, 0);
lean_inc_ref(v_traces_2702_);
lean_dec_ref(v_traceState_2701_);
v___x_2703_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2702_);
lean_dec_ref(v_traces_2702_);
v_sz_2704_ = lean_array_size(v___x_2703_);
v___x_2705_ = ((size_t)0ULL);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(v_sz_2704_, v___x_2705_, v___x_2703_);
v_msg_2707_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2707_, 0, v_data_2683_);
lean_ctor_set(v_msg_2707_, 1, v_msg_2685_);
lean_ctor_set(v_msg_2707_, 2, v___x_2706_);
v___x_2708_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2707_, v___y_2686_, v___y_2687_, v___x_2699_, v___y_2689_);
lean_dec_ref_known(v___x_2699_, 3);
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2747_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2747_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v_traceState_2714_; lean_object* v_env_2715_; lean_object* v_nextMacroScope_2716_; lean_object* v_ngen_2717_; lean_object* v_auxDeclNGen_2718_; lean_object* v_cache_2719_; lean_object* v_recordedDeps_2720_; lean_object* v_messages_2721_; lean_object* v_infoState_2722_; lean_object* v_snapshotTasks_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2746_; 
v___x_2713_ = lean_st_ref_take(v___y_2689_);
v_traceState_2714_ = lean_ctor_get(v___x_2713_, 4);
v_env_2715_ = lean_ctor_get(v___x_2713_, 0);
v_nextMacroScope_2716_ = lean_ctor_get(v___x_2713_, 1);
v_ngen_2717_ = lean_ctor_get(v___x_2713_, 2);
v_auxDeclNGen_2718_ = lean_ctor_get(v___x_2713_, 3);
v_cache_2719_ = lean_ctor_get(v___x_2713_, 5);
v_recordedDeps_2720_ = lean_ctor_get(v___x_2713_, 6);
v_messages_2721_ = lean_ctor_get(v___x_2713_, 7);
v_infoState_2722_ = lean_ctor_get(v___x_2713_, 8);
v_snapshotTasks_2723_ = lean_ctor_get(v___x_2713_, 9);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2725_ = v___x_2713_;
v_isShared_2726_ = v_isSharedCheck_2746_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_snapshotTasks_2723_);
lean_inc(v_infoState_2722_);
lean_inc(v_messages_2721_);
lean_inc(v_recordedDeps_2720_);
lean_inc(v_cache_2719_);
lean_inc(v_traceState_2714_);
lean_inc(v_auxDeclNGen_2718_);
lean_inc(v_ngen_2717_);
lean_inc(v_nextMacroScope_2716_);
lean_inc(v_env_2715_);
lean_dec(v___x_2713_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2746_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
uint64_t v_tid_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2744_; 
v_tid_2727_ = lean_ctor_get_uint64(v_traceState_2714_, sizeof(void*)*1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_traceState_2714_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; 
v_unused_2745_ = lean_ctor_get(v_traceState_2714_, 0);
lean_dec(v_unused_2745_);
v___x_2729_ = v_traceState_2714_;
v_isShared_2730_ = v_isSharedCheck_2744_;
goto v_resetjp_2728_;
}
else
{
lean_dec(v_traceState_2714_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2744_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2731_ = lean_box(0);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_ref_2684_);
lean_ctor_set(v___x_2732_, 1, v_a_2709_);
v___x_2733_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2682_, v___x_2732_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2733_);
v___x_2735_ = v___x_2729_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2733_);
lean_ctor_set_uint64(v_reuseFailAlloc_2743_, sizeof(void*)*1, v_tid_2727_);
v___x_2735_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2737_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 4, v___x_2735_);
v___x_2737_ = v___x_2725_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_env_2715_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_nextMacroScope_2716_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_ngen_2717_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_auxDeclNGen_2718_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2742_, 5, v_cache_2719_);
lean_ctor_set(v_reuseFailAlloc_2742_, 6, v_recordedDeps_2720_);
lean_ctor_set(v_reuseFailAlloc_2742_, 7, v_messages_2721_);
lean_ctor_set(v_reuseFailAlloc_2742_, 8, v_infoState_2722_);
lean_ctor_set(v_reuseFailAlloc_2742_, 9, v_snapshotTasks_2723_);
v___x_2737_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = lean_st_ref_put(v___y_2689_, v___x_2737_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2731_);
v___x_2740_ = v___x_2711_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2731_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(lean_object* v_oldTraces_2748_, lean_object* v_data_2749_, lean_object* v_ref_2750_, lean_object* v_msg_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_oldTraces_2748_, v_data_2749_, v_ref_2750_, v_msg_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(lean_object* v_opts_2758_, lean_object* v_opt_2759_){
_start:
{
lean_object* v_name_2760_; lean_object* v_defValue_2761_; lean_object* v_map_2762_; lean_object* v___x_2763_; 
v_name_2760_ = lean_ctor_get(v_opt_2759_, 0);
v_defValue_2761_ = lean_ctor_get(v_opt_2759_, 1);
v_map_2762_ = lean_ctor_get(v_opts_2758_, 0);
v___x_2763_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2762_, v_name_2760_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_inc(v_defValue_2761_);
return v_defValue_2761_;
}
else
{
lean_object* v_val_2764_; 
v_val_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v___x_2763_, 1);
if (lean_obj_tag(v_val_2764_) == 3)
{
lean_object* v_v_2765_; 
v_v_2765_ = lean_ctor_get(v_val_2764_, 0);
lean_inc(v_v_2765_);
lean_dec_ref_known(v_val_2764_, 1);
return v_v_2765_;
}
else
{
lean_dec(v_val_2764_);
lean_inc(v_defValue_2761_);
return v_defValue_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(lean_object* v_opts_2766_, lean_object* v_opt_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2766_, v_opt_2767_);
lean_dec_ref(v_opt_2767_);
lean_dec_ref(v_opts_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(lean_object* v_x_2769_){
_start:
{
if (lean_obj_tag(v_x_2769_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
v_a_2771_ = lean_ctor_get(v_x_2769_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_x_2769_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v_x_2769_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v_x_2769_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 1);
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v_a_2779_ = lean_ctor_get(v_x_2769_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_x_2769_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v_x_2769_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v_x_2769_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set_tag(v___x_2781_, 0);
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg___boxed(lean_object* v_x_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_x_2787_);
return v_res_2789_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0));
v___x_2792_ = l_Lean_stringToMessageData(v___x_2791_);
return v___x_2792_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2(void){
_start:
{
lean_object* v___x_2793_; double v___x_2794_; 
v___x_2793_ = lean_unsigned_to_nat(1000u);
v___x_2794_ = lean_float_of_nat(v___x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object* v_cls_2795_, uint8_t v_collapsed_2796_, lean_object* v_tag_2797_, lean_object* v_opts_2798_, uint8_t v_clsEnabled_2799_, lean_object* v_oldTraces_2800_, lean_object* v_msg_2801_, lean_object* v_resStartStop_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_fst_2808_; lean_object* v_snd_2809_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v_data_2813_; lean_object* v_fst_2824_; lean_object* v_snd_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___y_2829_; lean_object* v_a_2830_; uint8_t v___y_2845_; double v___y_2877_; 
v_fst_2808_ = lean_ctor_get(v_resStartStop_2802_, 0);
lean_inc(v_fst_2808_);
v_snd_2809_ = lean_ctor_get(v_resStartStop_2802_, 1);
lean_inc(v_snd_2809_);
lean_dec_ref(v_resStartStop_2802_);
v_fst_2824_ = lean_ctor_get(v_snd_2809_, 0);
lean_inc(v_fst_2824_);
v_snd_2825_ = lean_ctor_get(v_snd_2809_, 1);
lean_inc(v_snd_2825_);
lean_dec(v_snd_2809_);
v___x_2826_ = l_Lean_trace_profiler;
v___x_2827_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2798_, v___x_2826_);
if (v___x_2827_ == 0)
{
v___y_2845_ = v___x_2827_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2882_; uint8_t v___x_2883_; 
v___x_2882_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2883_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2798_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; double v___x_2886_; double v___x_2887_; double v___x_2888_; 
v___x_2884_ = l_Lean_trace_profiler_threshold;
v___x_2885_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2798_, v___x_2884_);
v___x_2886_ = lean_float_of_nat(v___x_2885_);
v___x_2887_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2);
v___x_2888_ = lean_float_div(v___x_2886_, v___x_2887_);
v___y_2877_ = v___x_2888_;
goto v___jp_2876_;
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; double v___x_2891_; 
v___x_2889_ = l_Lean_trace_profiler_threshold;
v___x_2890_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2798_, v___x_2889_);
v___x_2891_ = lean_float_of_nat(v___x_2890_);
v___y_2877_ = v___x_2891_;
goto v___jp_2876_;
}
}
v___jp_2810_:
{
lean_object* v___x_2814_; 
lean_inc(v___y_2812_);
v___x_2814_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_oldTraces_2800_, v_data_2813_, v___y_2812_, v___y_2811_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v___x_2815_; 
lean_dec_ref_known(v___x_2814_, 1);
v___x_2815_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_fst_2808_);
return v___x_2815_;
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_fst_2808_);
v_a_2816_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2814_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2814_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
v___jp_2828_:
{
uint8_t v_result_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; double v___x_2834_; lean_object* v_data_2835_; 
v_result_2831_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_fst_2808_);
v___x_2832_ = lean_box(v_result_2831_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
v___x_2834_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
lean_inc_ref(v_tag_2797_);
lean_inc_ref(v___x_2833_);
lean_inc(v_cls_2795_);
v_data_2835_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2835_, 0, v_cls_2795_);
lean_ctor_set(v_data_2835_, 1, v___x_2833_);
lean_ctor_set(v_data_2835_, 2, v_tag_2797_);
lean_ctor_set_float(v_data_2835_, sizeof(void*)*3, v___x_2834_);
lean_ctor_set_float(v_data_2835_, sizeof(void*)*3 + 8, v___x_2834_);
lean_ctor_set_uint8(v_data_2835_, sizeof(void*)*3 + 16, v_collapsed_2796_);
if (v___x_2827_ == 0)
{
lean_dec_ref_known(v___x_2833_, 1);
lean_dec(v_snd_2825_);
lean_dec(v_fst_2824_);
lean_dec_ref(v_tag_2797_);
lean_dec(v_cls_2795_);
v___y_2811_ = v_a_2830_;
v___y_2812_ = v___y_2829_;
v_data_2813_ = v_data_2835_;
goto v___jp_2810_;
}
else
{
lean_object* v_data_2836_; double v___x_2837_; double v___x_2838_; 
lean_dec_ref_known(v_data_2835_, 3);
v_data_2836_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2836_, 0, v_cls_2795_);
lean_ctor_set(v_data_2836_, 1, v___x_2833_);
lean_ctor_set(v_data_2836_, 2, v_tag_2797_);
v___x_2837_ = lean_unbox_float(v_fst_2824_);
lean_dec(v_fst_2824_);
lean_ctor_set_float(v_data_2836_, sizeof(void*)*3, v___x_2837_);
v___x_2838_ = lean_unbox_float(v_snd_2825_);
lean_dec(v_snd_2825_);
lean_ctor_set_float(v_data_2836_, sizeof(void*)*3 + 8, v___x_2838_);
lean_ctor_set_uint8(v_data_2836_, sizeof(void*)*3 + 16, v_collapsed_2796_);
v___y_2811_ = v_a_2830_;
v___y_2812_ = v___y_2829_;
v_data_2813_ = v_data_2836_;
goto v___jp_2810_;
}
}
v___jp_2839_:
{
lean_object* v_ref_2840_; lean_object* v___x_2841_; 
v_ref_2840_ = lean_ctor_get(v___y_2805_, 2);
lean_inc(v___y_2806_);
lean_inc_ref(v___y_2805_);
lean_inc(v___y_2804_);
lean_inc_ref(v___y_2803_);
lean_inc(v_fst_2808_);
v___x_2841_ = lean_apply_6(v_msg_2801_, v_fst_2808_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, lean_box(0));
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v___y_2829_ = v_ref_2840_;
v_a_2830_ = v_a_2842_;
goto v___jp_2828_;
}
else
{
lean_object* v___x_2843_; 
lean_dec_ref_known(v___x_2841_, 1);
v___x_2843_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1);
v___y_2829_ = v_ref_2840_;
v_a_2830_ = v___x_2843_;
goto v___jp_2828_;
}
}
v___jp_2844_:
{
if (v_clsEnabled_2799_ == 0)
{
if (v___y_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v_traceState_2847_; lean_object* v_env_2848_; lean_object* v_nextMacroScope_2849_; lean_object* v_ngen_2850_; lean_object* v_auxDeclNGen_2851_; lean_object* v_cache_2852_; lean_object* v_recordedDeps_2853_; lean_object* v_messages_2854_; lean_object* v_infoState_2855_; lean_object* v_snapshotTasks_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2875_; 
lean_dec(v_snd_2825_);
lean_dec(v_fst_2824_);
lean_dec_ref(v_msg_2801_);
lean_dec_ref(v_tag_2797_);
lean_dec(v_cls_2795_);
v___x_2846_ = lean_st_ref_take(v___y_2806_);
v_traceState_2847_ = lean_ctor_get(v___x_2846_, 4);
v_env_2848_ = lean_ctor_get(v___x_2846_, 0);
v_nextMacroScope_2849_ = lean_ctor_get(v___x_2846_, 1);
v_ngen_2850_ = lean_ctor_get(v___x_2846_, 2);
v_auxDeclNGen_2851_ = lean_ctor_get(v___x_2846_, 3);
v_cache_2852_ = lean_ctor_get(v___x_2846_, 5);
v_recordedDeps_2853_ = lean_ctor_get(v___x_2846_, 6);
v_messages_2854_ = lean_ctor_get(v___x_2846_, 7);
v_infoState_2855_ = lean_ctor_get(v___x_2846_, 8);
v_snapshotTasks_2856_ = lean_ctor_get(v___x_2846_, 9);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2858_ = v___x_2846_;
v_isShared_2859_ = v_isSharedCheck_2875_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_snapshotTasks_2856_);
lean_inc(v_infoState_2855_);
lean_inc(v_messages_2854_);
lean_inc(v_recordedDeps_2853_);
lean_inc(v_cache_2852_);
lean_inc(v_traceState_2847_);
lean_inc(v_auxDeclNGen_2851_);
lean_inc(v_ngen_2850_);
lean_inc(v_nextMacroScope_2849_);
lean_inc(v_env_2848_);
lean_dec(v___x_2846_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2875_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
uint64_t v_tid_2860_; lean_object* v_traces_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2874_; 
v_tid_2860_ = lean_ctor_get_uint64(v_traceState_2847_, sizeof(void*)*1);
v_traces_2861_ = lean_ctor_get(v_traceState_2847_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_traceState_2847_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2863_ = v_traceState_2847_;
v_isShared_2864_ = v_isSharedCheck_2874_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_traces_2861_);
lean_dec(v_traceState_2847_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2874_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2865_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2800_, v_traces_2861_);
lean_dec_ref(v_traces_2861_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2865_);
v___x_2867_ = v___x_2863_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2865_);
lean_ctor_set_uint64(v_reuseFailAlloc_2873_, sizeof(void*)*1, v_tid_2860_);
v___x_2867_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2869_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 4, v___x_2867_);
v___x_2869_ = v___x_2858_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_env_2848_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_nextMacroScope_2849_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_ngen_2850_);
lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_auxDeclNGen_2851_);
lean_ctor_set(v_reuseFailAlloc_2872_, 4, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2872_, 5, v_cache_2852_);
lean_ctor_set(v_reuseFailAlloc_2872_, 6, v_recordedDeps_2853_);
lean_ctor_set(v_reuseFailAlloc_2872_, 7, v_messages_2854_);
lean_ctor_set(v_reuseFailAlloc_2872_, 8, v_infoState_2855_);
lean_ctor_set(v_reuseFailAlloc_2872_, 9, v_snapshotTasks_2856_);
v___x_2869_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_st_ref_put(v___y_2806_, v___x_2869_);
v___x_2871_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_fst_2808_);
return v___x_2871_;
}
}
}
}
}
else
{
goto v___jp_2839_;
}
}
else
{
goto v___jp_2839_;
}
}
v___jp_2876_:
{
double v___x_2878_; double v___x_2879_; double v___x_2880_; uint8_t v___x_2881_; 
v___x_2878_ = lean_unbox_float(v_snd_2825_);
v___x_2879_ = lean_unbox_float(v_fst_2824_);
v___x_2880_ = lean_float_sub(v___x_2878_, v___x_2879_);
v___x_2881_ = lean_float_decLt(v___y_2877_, v___x_2880_);
v___y_2845_ = v___x_2881_;
goto v___jp_2844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object* v_cls_2892_, lean_object* v_collapsed_2893_, lean_object* v_tag_2894_, lean_object* v_opts_2895_, lean_object* v_clsEnabled_2896_, lean_object* v_oldTraces_2897_, lean_object* v_msg_2898_, lean_object* v_resStartStop_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
uint8_t v_collapsed_boxed_2905_; uint8_t v_clsEnabled_boxed_2906_; lean_object* v_res_2907_; 
v_collapsed_boxed_2905_ = lean_unbox(v_collapsed_2893_);
v_clsEnabled_boxed_2906_ = lean_unbox(v_clsEnabled_2896_);
v_res_2907_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2892_, v_collapsed_boxed_2905_, v_tag_2894_, v_opts_2895_, v_clsEnabled_boxed_2906_, v_oldTraces_2897_, v_msg_2898_, v_resStartStop_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec_ref(v_opts_2895_);
return v_res_2907_;
}
}
static double _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0(void){
_start:
{
lean_object* v___x_2908_; double v___x_2909_; 
v___x_2908_ = lean_unsigned_to_nat(1000000000u);
v___x_2909_ = lean_float_of_nat(v___x_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object* v_t_2910_, lean_object* v_s_2911_, lean_object* v_candidate_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v_toCold_2918_; lean_object* v_options_2919_; lean_object* v_inheritedTraceOptions_2920_; uint8_t v_hasTrace_2921_; uint8_t v___x_2922_; 
v_toCold_2918_ = lean_ctor_get(v_a_2915_, 0);
v_options_2919_ = lean_ctor_get(v_toCold_2918_, 2);
v_inheritedTraceOptions_2920_ = lean_ctor_get(v_toCold_2918_, 11);
v_hasTrace_2921_ = lean_ctor_get_uint8(v_options_2919_, sizeof(void*)*1);
v___x_2922_ = 1;
if (v_hasTrace_2921_ == 0)
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2912_, v_t_2910_, v_s_2911_, v___x_2922_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
return v___x_2923_;
}
else
{
lean_object* v___f_2924_; lean_object* v_cls_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v_a_2932_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v_a_2947_; 
lean_inc_ref(v_s_2911_);
lean_inc_ref(v_t_2910_);
lean_inc(v_candidate_2912_);
v___f_2924_ = lean_alloc_closure((void*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2924_, 0, v_candidate_2912_);
lean_closure_set(v___f_2924_, 1, v_t_2910_);
lean_closure_set(v___f_2924_, 2, v_s_2911_);
v_cls_2925_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2926_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_2927_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7);
v___x_2928_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2920_, v_options_2919_, v___x_2927_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2997_ = l_Lean_trace_profiler;
v___x_2998_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2919_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; 
lean_dec_ref(v___f_2924_);
v___x_2999_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2912_, v_t_2910_, v_s_2911_, v___x_2922_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
return v___x_2999_;
}
else
{
goto v___jp_2956_;
}
}
else
{
goto v___jp_2956_;
}
v___jp_2929_:
{
lean_object* v___x_2933_; double v___x_2934_; double v___x_2935_; double v___x_2936_; double v___x_2937_; double v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2933_ = lean_io_mono_nanos_now();
v___x_2934_ = lean_float_of_nat(v___y_2930_);
v___x_2935_ = lean_float_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0);
v___x_2936_ = lean_float_div(v___x_2934_, v___x_2935_);
v___x_2937_ = lean_float_of_nat(v___x_2933_);
v___x_2938_ = lean_float_div(v___x_2937_, v___x_2935_);
v___x_2939_ = lean_box_float(v___x_2936_);
v___x_2940_ = lean_box_float(v___x_2938_);
v___x_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2939_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v_a_2932_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2925_, v___x_2922_, v___x_2926_, v_options_2919_, v___x_2928_, v___y_2931_, v___f_2924_, v___x_2942_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
return v___x_2943_;
}
v___jp_2944_:
{
lean_object* v___x_2948_; double v___x_2949_; double v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2948_ = lean_io_get_num_heartbeats();
v___x_2949_ = lean_float_of_nat(v___y_2946_);
v___x_2950_ = lean_float_of_nat(v___x_2948_);
v___x_2951_ = lean_box_float(v___x_2949_);
v___x_2952_ = lean_box_float(v___x_2950_);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2951_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v_a_2947_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2925_, v___x_2922_, v___x_2926_, v_options_2919_, v___x_2928_, v___y_2945_, v___f_2924_, v___x_2954_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
return v___x_2955_;
}
v___jp_2956_:
{
lean_object* v___x_2957_; lean_object* v_a_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2957_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v_a_2916_);
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref(v___x_2957_);
v___x_2959_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2960_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2919_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_io_mono_nanos_now();
v___x_2962_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2912_, v_t_2910_, v_s_2911_, v___x_2922_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2962_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2962_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 1);
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
v___y_2930_ = v___x_2961_;
v___y_2931_ = v_a_2958_;
v_a_2932_ = v___x_2968_;
goto v___jp_2929_;
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
v_a_2971_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2962_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2962_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set_tag(v___x_2973_, 0);
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
v___y_2930_ = v___x_2961_;
v___y_2931_ = v_a_2958_;
v_a_2932_ = v___x_2976_;
goto v___jp_2929_;
}
}
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_io_get_num_heartbeats();
v___x_2980_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2912_, v_t_2910_, v_s_2911_, v___x_2922_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2980_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 1);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
v___y_2945_ = v_a_2958_;
v___y_2946_ = v___x_2979_;
v_a_2947_ = v___x_2986_;
goto v___jp_2944_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_a_2989_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2980_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2980_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set_tag(v___x_2991_, 0);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
v___y_2945_ = v_a_2958_;
v___y_2946_ = v___x_2979_;
v_a_2947_ = v___x_2994_;
goto v___jp_2944_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object* v_t_3000_, lean_object* v_s_3001_, lean_object* v_candidate_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_3000_, v_s_3001_, v_candidate_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object* v_as_3009_, lean_object* v_as_x27_3010_, lean_object* v_b_3011_, lean_object* v_a_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_3010_, v_b_3011_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object* v_as_3019_, lean_object* v_as_x27_3020_, lean_object* v_b_3021_, lean_object* v_a_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(v_as_3019_, v_as_x27_3020_, v_b_3021_, v_a_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v_as_x27_3020_);
lean_dec(v_as_3019_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(lean_object* v_00_u03b1_3029_, lean_object* v_x_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_x_3030_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(lean_object* v_00_u03b1_3037_, lean_object* v_x_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_00_u03b1_3037_, v_x_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(lean_object* v_t_3045_, lean_object* v_s_3046_, uint8_t v___x_3047_, lean_object* v_as_3048_, size_t v_sz_3049_, size_t v_i_3050_, lean_object* v_b_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
uint8_t v___x_3057_; 
v___x_3057_ = lean_usize_dec_lt(v_i_3050_, v_sz_3049_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; 
lean_dec_ref(v_s_3046_);
lean_dec_ref(v_t_3045_);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v_b_3051_);
return v___x_3058_;
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v_a_3061_; lean_object* v___x_3062_; 
lean_dec_ref(v_b_3051_);
v___x_3059_ = lean_box(0);
v___x_3060_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_a_3061_ = lean_array_uget_borrowed(v_as_3048_, v_i_3050_);
lean_inc(v_a_3061_);
lean_inc_ref(v_s_3046_);
lean_inc_ref(v_t_3045_);
v___x_3062_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_3045_, v_s_3046_, v_a_3061_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3077_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3065_ = v___x_3062_;
v_isShared_3066_ = v_isSharedCheck_3077_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3062_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3077_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
uint8_t v___x_3067_; 
v___x_3067_ = lean_unbox(v_a_3063_);
lean_dec(v_a_3063_);
if (v___x_3067_ == 0)
{
size_t v___x_3068_; size_t v___x_3069_; 
lean_del_object(v___x_3065_);
v___x_3068_ = ((size_t)1ULL);
v___x_3069_ = lean_usize_add(v_i_3050_, v___x_3068_);
v_i_3050_ = v___x_3069_;
v_b_3051_ = v___x_3060_;
goto _start;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
lean_dec_ref(v_s_3046_);
lean_dec_ref(v_t_3045_);
v___x_3071_ = lean_box(v___x_3047_);
v___x_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3059_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3073_);
v___x_3075_ = v___x_3065_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec_ref(v_s_3046_);
lean_dec_ref(v_t_3045_);
v_a_3078_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3062_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3062_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object* v_t_3086_, lean_object* v_s_3087_, lean_object* v___x_3088_, lean_object* v_as_3089_, lean_object* v_sz_3090_, lean_object* v_i_3091_, lean_object* v_b_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
uint8_t v___x_2922__boxed_3098_; size_t v_sz_boxed_3099_; size_t v_i_boxed_3100_; lean_object* v_res_3101_; 
v___x_2922__boxed_3098_ = lean_unbox(v___x_3088_);
v_sz_boxed_3099_ = lean_unbox_usize(v_sz_3090_);
lean_dec(v_sz_3090_);
v_i_boxed_3100_ = lean_unbox_usize(v_i_3091_);
lean_dec(v_i_3091_);
v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_3086_, v_s_3087_, v___x_2922__boxed_3098_, v_as_3089_, v_sz_boxed_3099_, v_i_boxed_3100_, v_b_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec_ref(v_as_3089_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* v_t_3102_, lean_object* v_s_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v_toCold_3183_; lean_object* v_options_3184_; uint8_t v_hasTrace_3185_; 
v_toCold_3183_ = lean_ctor_get(v_a_3106_, 0);
v_options_3184_ = lean_ctor_get(v_toCold_3183_, 2);
v_hasTrace_3185_ = lean_ctor_get_uint8(v_options_3184_, sizeof(void*)*1);
if (v_hasTrace_3185_ == 0)
{
v___y_3110_ = v_a_3104_;
v___y_3111_ = v_a_3105_;
v___y_3112_ = v_a_3106_;
v___y_3113_ = v_a_3107_;
goto v___jp_3109_;
}
else
{
lean_object* v_inheritedTraceOptions_3186_; lean_object* v_cls_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v_inheritedTraceOptions_3186_ = lean_ctor_get(v_toCold_3183_, 11);
v_cls_3187_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_3188_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7);
v___x_3189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3186_, v_options_3184_, v___x_3188_);
if (v___x_3189_ == 0)
{
v___y_3110_ = v_a_3104_;
v___y_3111_ = v_a_3105_;
v___y_3112_ = v_a_3106_;
v___y_3113_ = v_a_3107_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_inc_ref(v_t_3102_);
v___x_3190_ = l_Lean_MessageData_ofExpr(v_t_3102_);
v___x_3191_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_3192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
lean_inc_ref(v_s_3103_);
v___x_3193_ = l_Lean_MessageData_ofExpr(v_s_3103_);
v___x_3194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_3187_, v___x_3194_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_dec_ref_known(v___x_3195_, 1);
v___y_3110_ = v_a_3104_;
v___y_3111_ = v_a_3105_;
v___y_3112_ = v_a_3106_;
v___y_3113_ = v_a_3107_;
goto v___jp_3109_;
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v_s_3103_);
lean_dec_ref(v_t_3102_);
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
v___jp_3109_:
{
lean_object* v___x_3114_; uint8_t v_unificationHints_3115_; 
v___x_3114_ = l_Lean_Meta_Context_config(v___y_3110_);
v_unificationHints_3115_ = lean_ctor_get_uint8(v___x_3114_, 5);
lean_dec_ref(v___x_3114_);
if (v_unificationHints_3115_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec_ref(v_s_3103_);
lean_dec_ref(v_t_3102_);
v___x_3116_ = lean_box(v_unificationHints_3115_);
v___x_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
return v___x_3117_;
}
else
{
uint8_t v___x_3118_; 
v___x_3118_ = l_Lean_Expr_isMVar(v_t_3102_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
v___x_3119_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints(v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3121_; lean_object* v_config_3122_; uint8_t v_trackZetaDelta_3123_; lean_object* v_zetaDeltaSet_3124_; lean_object* v_lctx_3125_; lean_object* v_localInstances_3126_; lean_object* v_defEqCtx_x3f_3127_; lean_object* v_synthPendingDepth_3128_; lean_object* v_customCanUnfoldPredicate_x3f_3129_; uint8_t v_univApprox_3130_; uint8_t v_inTypeClassResolution_3131_; uint8_t v_cacheInferType_3132_; uint64_t v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_3122_ = lean_ctor_get(v___x_3121_, 0);
v_trackZetaDelta_3123_ = lean_ctor_get_uint8(v___y_3110_, sizeof(void*)*7);
v_zetaDeltaSet_3124_ = lean_ctor_get(v___y_3110_, 1);
v_lctx_3125_ = lean_ctor_get(v___y_3110_, 2);
v_localInstances_3126_ = lean_ctor_get(v___y_3110_, 3);
v_defEqCtx_x3f_3127_ = lean_ctor_get(v___y_3110_, 4);
v_synthPendingDepth_3128_ = lean_ctor_get(v___y_3110_, 5);
v_customCanUnfoldPredicate_x3f_3129_ = lean_ctor_get(v___y_3110_, 6);
v_univApprox_3130_ = lean_ctor_get_uint8(v___y_3110_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3131_ = lean_ctor_get_uint8(v___y_3110_, sizeof(void*)*7 + 2);
v_cacheInferType_3132_ = lean_ctor_get_uint8(v___y_3110_, sizeof(void*)*7 + 3);
v___x_3133_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_3122_);
lean_inc_ref(v_config_3122_);
v___x_3134_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3134_, 0, v_config_3122_);
lean_ctor_set_uint64(v___x_3134_, sizeof(void*)*1, v___x_3133_);
lean_inc(v_customCanUnfoldPredicate_x3f_3129_);
lean_inc(v_synthPendingDepth_3128_);
lean_inc(v_defEqCtx_x3f_3127_);
lean_inc_ref(v_localInstances_3126_);
lean_inc_ref(v_lctx_3125_);
lean_inc(v_zetaDeltaSet_3124_);
v___x_3135_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
lean_ctor_set(v___x_3135_, 1, v_zetaDeltaSet_3124_);
lean_ctor_set(v___x_3135_, 2, v_lctx_3125_);
lean_ctor_set(v___x_3135_, 3, v_localInstances_3126_);
lean_ctor_set(v___x_3135_, 4, v_defEqCtx_x3f_3127_);
lean_ctor_set(v___x_3135_, 5, v_synthPendingDepth_3128_);
lean_ctor_set(v___x_3135_, 6, v_customCanUnfoldPredicate_x3f_3129_);
lean_ctor_set_uint8(v___x_3135_, sizeof(void*)*7, v_trackZetaDelta_3123_);
lean_ctor_set_uint8(v___x_3135_, sizeof(void*)*7 + 1, v_univApprox_3130_);
lean_ctor_set_uint8(v___x_3135_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3131_);
lean_ctor_set_uint8(v___x_3135_, sizeof(void*)*7 + 3, v_cacheInferType_3132_);
lean_inc_ref(v_t_3102_);
v___x_3136_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_a_3120_, v_t_3102_, v___x_3135_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec_ref_known(v___x_3135_, 7);
lean_dec(v_a_3120_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3138_; size_t v_sz_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3136_, 1);
v___x_3138_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_sz_3139_ = lean_array_size(v_a_3137_);
v___x_3140_ = ((size_t)0ULL);
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_3102_, v_s_3103_, v_unificationHints_3115_, v_a_3137_, v_sz_3139_, v___x_3140_, v___x_3138_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v_a_3137_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3155_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3155_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3155_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v_fst_3146_; 
v_fst_3146_ = lean_ctor_get(v_a_3142_, 0);
lean_inc(v_fst_3146_);
lean_dec(v_a_3142_);
if (lean_obj_tag(v_fst_3146_) == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3147_ = lean_box(v___x_3118_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3147_);
v___x_3149_ = v___x_3144_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
else
{
lean_object* v_val_3151_; lean_object* v___x_3153_; 
v_val_3151_ = lean_ctor_get(v_fst_3146_, 0);
lean_inc(v_val_3151_);
lean_dec_ref_known(v_fst_3146_, 1);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v_val_3151_);
v___x_3153_ = v___x_3144_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_val_3151_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
v_a_3156_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3141_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3141_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v_s_3103_);
lean_dec_ref(v_t_3102_);
v_a_3164_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3136_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3136_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec_ref(v_s_3103_);
lean_dec_ref(v_t_3102_);
v_a_3172_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3119_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3119_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
uint8_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec_ref(v_s_3103_);
lean_dec_ref(v_t_3102_);
v___x_3180_ = 0;
v___x_3181_ = lean_box(v___x_3180_);
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
return v___x_3182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___boxed(lean_object* v_t_3204_, lean_object* v_s_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_Meta_tryUnificationHints(v_t_3204_, v_s_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
return v_res_3211_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_unsigned_to_nat(2674080740u);
v___x_3213_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3214_ = l_Lean_Name_num___override(v___x_3213_, v___x_3212_);
return v___x_3214_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3216_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3217_ = l_Lean_Name_str___override(v___x_3216_, v___x_3215_);
return v___x_3217_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3219_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3220_ = l_Lean_Name_str___override(v___x_3219_, v___x_3218_);
return v___x_3220_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = lean_unsigned_to_nat(2u);
v___x_3222_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3223_ = l_Lean_Name_num___override(v___x_3222_, v___x_3221_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3225_; uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3225_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_3226_ = 0;
v___x_3227_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3228_ = l_Lean_registerTraceClass(v___x_3225_, v___x_3226_, v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(lean_object* v_a_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
return v_res_3230_;
}
}
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_UnificationHint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedUnificationHints_default = _init_l_Lean_Meta_instInhabitedUnificationHints_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints_default);
l_Lean_Meta_instInhabitedUnificationHints = _init_l_Lean_Meta_instInhabitedUnificationHints();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config);
res = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3890461423____hygCtx___hyg_2_();
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
