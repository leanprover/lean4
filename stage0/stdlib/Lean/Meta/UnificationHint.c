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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
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
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 0, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 1, 0, 0, 0)}};
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__26;
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
static const lean_ctor_object l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 1, 0, 0, 0)}};
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
v___x_1122_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v___x_1120_);
lean_ctor_set(v___x_1122_, 2, v___x_1119_);
lean_ctor_set(v___x_1122_, 3, v___x_1120_);
lean_ctor_set(v___x_1122_, 4, v___x_1120_);
lean_ctor_set(v___x_1122_, 5, v___x_1120_);
lean_ctor_set(v___x_1122_, 6, v___x_1118_);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__20(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__19));
v___x_1245_ = l_Lean_stringToMessageData(v___x_1244_);
return v___x_1245_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__22(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__21));
v___x_1248_ = l_Lean_stringToMessageData(v___x_1247_);
return v___x_1248_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__24(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__23));
v___x_1251_ = l_Lean_stringToMessageData(v___x_1250_);
return v___x_1251_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__26(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__25));
v___x_1254_ = l_Lean_stringToMessageData(v___x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_msg_1255_, lean_object* v_declHint_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_env_1261_; uint8_t v___x_1262_; 
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_st_ref_get(v___y_1257_);
v_env_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_ref(v_env_1261_);
lean_dec(v___x_1260_);
v___x_1262_ = l_Lean_Name_isAnonymous(v_declHint_1256_);
if (v___x_1262_ == 0)
{
uint8_t v_isExporting_1263_; 
v_isExporting_1263_ = lean_ctor_get_uint8(v_env_1261_, sizeof(void*)*13);
if (v_isExporting_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v_env_1261_);
lean_dec(v_declHint_1256_);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_msg_1255_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
lean_inc_ref(v_env_1261_);
v___x_1265_ = l_Lean_Environment_setExporting(v_env_1261_, v___x_1262_);
lean_inc(v_declHint_1256_);
lean_inc_ref(v___x_1265_);
v___x_1266_ = l_Lean_Environment_contains(v___x_1265_, v_declHint_1256_, v_isExporting_1263_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v___x_1265_);
lean_dec_ref(v_env_1261_);
lean_dec(v_declHint_1256_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_msg_1255_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_c_1273_; lean_object* v___x_1274_; 
v___x_1268_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_1269_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4);
v___x_1270_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1265_);
v___x_1271_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1265_);
lean_ctor_set(v___x_1271_, 1, v___x_1268_);
lean_ctor_set(v___x_1271_, 2, v___x_1269_);
lean_ctor_set(v___x_1271_, 3, v___x_1270_);
lean_inc(v_declHint_1256_);
v___x_1272_ = l_Lean_MessageData_ofConstName(v_declHint_1256_, v___x_1262_);
v_c_1273_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1273_, 0, v___x_1271_);
lean_ctor_set(v_c_1273_, 1, v___x_1272_);
v___x_1274_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1265_, v_declHint_1256_);
lean_dec_ref(v___x_1265_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref(v_env_1261_);
lean_dec(v_declHint_1256_);
v___x_1275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_c_1273_);
v___x_1277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__8);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_MessageData_note(v___x_1278_);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_msg_1255_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
else
{
lean_object* v_val_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1335_; 
v_val_1282_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1284_ = v___x_1274_;
v_isShared_1285_ = v_isSharedCheck_1335_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_val_1282_);
lean_dec(v___x_1274_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1335_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v_modules_1287_; lean_object* v_moduleNames_1288_; lean_object* v_mod_1289_; uint8_t v___x_1304_; 
v___x_1286_ = l_Lean_Environment_header(v_env_1261_);
lean_dec_ref(v_env_1261_);
v_modules_1287_ = lean_ctor_get(v___x_1286_, 3);
lean_inc_ref(v_modules_1287_);
v_moduleNames_1288_ = lean_ctor_get(v___x_1286_, 4);
lean_inc_ref(v_moduleNames_1288_);
lean_dec_ref(v___x_1286_);
v_mod_1289_ = lean_array_get(v___x_1259_, v_moduleNames_1288_, v_val_1282_);
lean_dec_ref(v_moduleNames_1288_);
v___x_1304_ = l_Lean_isPrivateName(v_declHint_1256_);
lean_dec(v_declHint_1256_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = lean_array_get_size(v_modules_1287_);
v___x_1306_ = lean_nat_dec_lt(v_val_1282_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v_modules_1287_);
lean_dec(v_val_1282_);
goto v___jp_1290_;
}
else
{
lean_object* v___x_1307_; lean_object* v_toImport_1308_; uint8_t v_isExported_1309_; 
v___x_1307_ = lean_array_fget(v_modules_1287_, v_val_1282_);
lean_dec(v_val_1282_);
lean_dec_ref(v_modules_1287_);
v_toImport_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc_ref(v_toImport_1308_);
lean_dec(v___x_1307_);
v_isExported_1309_ = lean_ctor_get_uint8(v_toImport_1308_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1308_);
if (v_isExported_1309_ == 0)
{
goto v___jp_1290_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_del_object(v___x_1284_);
v___x_1310_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__16);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_c_1273_);
v___x_1312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__18);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_MessageData_ofName(v_mod_1289_);
lean_inc_ref(v___x_1314_);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__20);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___x_1314_);
v___x_1319_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__22);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = l_Lean_MessageData_note(v___x_1320_);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_msg_1255_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
}
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v_modules_1287_);
lean_del_object(v___x_1284_);
lean_dec(v_val_1282_);
v___x_1324_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__6);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v_c_1273_);
v___x_1326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__24);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = l_Lean_MessageData_ofName(v_mod_1289_);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__26);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_MessageData_note(v___x_1331_);
v___x_1333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_msg_1255_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
v___jp_1290_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1291_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__10);
v___x_1292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v_c_1273_);
v___x_1293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__12);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = l_Lean_MessageData_ofName(v_mod_1289_);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__14);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = l_Lean_MessageData_note(v___x_1298_);
v___x_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_msg_1255_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1300_);
v___x_1302_ = v___x_1284_;
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
lean_object* v___x_1336_; 
lean_dec_ref(v_env_1261_);
lean_dec(v_declHint_1256_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_msg_1255_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1337_, lean_object* v_declHint_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg(v_msg_1337_, v_declHint_1338_, v___y_1339_);
lean_dec(v___y_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object* v_msg_1342_, lean_object* v_declHint_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1359_; 
v___x_1349_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg(v_msg_1342_, v_declHint_1343_, v___y_1347_);
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1359_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1359_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1354_ = l_Lean_unknownIdentifierMessageTag;
v___x_1355_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_a_1350_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1355_);
v___x_1357_ = v___x_1352_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object* v_msg_1360_, lean_object* v_declHint_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7(v_msg_1360_, v_declHint_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1368_, lean_object* v_msg_1369_, lean_object* v_declHint_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v_a_1377_; lean_object* v___x_1378_; 
v___x_1376_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7(v_msg_1369_, v_declHint_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_ref_1368_, v_a_1377_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1379_, lean_object* v_msg_1380_, lean_object* v_declHint_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1379_, v_msg_1380_, v_declHint_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v_ref_1379_);
return v_res_1387_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1390_ = l_Lean_stringToMessageData(v___x_1389_);
return v___x_1390_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1393_ = l_Lean_stringToMessageData(v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1394_, lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1401_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1402_ = 0;
lean_inc(v_constName_1395_);
v___x_1403_ = l_Lean_MessageData_ofConstName(v_constName_1395_, v___x_1402_);
v___x_1404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1401_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1394_, v___x_1406_, v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1408_, lean_object* v_constName_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg(v_ref_1408_, v_constName_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v_ref_1408_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(lean_object* v_constName_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_ref_1422_; lean_object* v___x_1423_; 
v_ref_1422_ = lean_ctor_get(v___y_1419_, 2);
v___x_1423_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg(v_ref_1422_, v_constName_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(lean_object* v_constName_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v_env_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1437_ = lean_st_ref_get(v___y_1435_);
v_env_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_ref(v_env_1438_);
lean_dec(v___x_1437_);
v___x_1439_ = 0;
lean_inc(v_constName_1431_);
v___x_1440_ = l_Lean_Environment_find_x3f(v_env_1438_, v_constName_1431_, v___x_1439_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1441_;
}
else
{
lean_object* v_val_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_constName_1431_);
v_val_1442_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1440_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_val_1442_);
lean_dec(v___x_1440_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 0);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_val_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(lean_object* v_constName_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_constName_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1456_;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l_Lean_Meta_addUnificationHint___lam__0___closed__0));
v___x_1459_ = l_Lean_stringToMessageData(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object* v_declName_1460_, uint8_t v_kind_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
lean_inc(v_declName_1460_);
v___x_1467_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_declName_1460_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1467_, 1);
v___x_1469_ = 0;
v___x_1470_ = l_Lean_ConstantInfo_value_x3f(v_a_1468_, v___x_1469_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec(v_declName_1460_);
v___x_1471_ = lean_obj_once(&l_Lean_Meta_addUnificationHint___lam__0___closed__1, &l_Lean_Meta_addUnificationHint___lam__0___closed__1_once, _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1);
v___x_1472_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_1471_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1472_;
}
else
{
lean_object* v_val_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_val_1473_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1473_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1474_ = lean_box(0);
v___x_1475_ = l_Lean_Meta_lambdaMetaTelescope(v_val_1473_, v___x_1474_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v_val_1473_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_snd_1477_; lean_object* v_snd_1478_; lean_object* v___x_1479_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v_snd_1477_ = lean_ctor_get(v_a_1476_, 1);
lean_inc(v_snd_1477_);
lean_dec(v_a_1476_);
v_snd_1478_ = lean_ctor_get(v_snd_1477_, 1);
lean_inc(v_snd_1478_);
lean_dec(v_snd_1477_);
v___x_1479_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_1478_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; 
lean_dec(v_declName_1460_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1481_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_a_1480_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1481_;
}
else
{
lean_object* v_a_1482_; lean_object* v_pattern_1483_; lean_object* v_lhs_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1519_; 
v_a_1482_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1479_, 1);
v_pattern_1483_ = lean_ctor_get(v_a_1482_, 0);
lean_inc_ref(v_pattern_1483_);
v_lhs_1484_ = lean_ctor_get(v_pattern_1483_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_pattern_1483_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_pattern_1483_, 1);
lean_dec(v_unused_1520_);
v___x_1486_ = v_pattern_1483_;
v_isShared_1487_ = v_isSharedCheck_1519_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_lhs_1484_);
lean_dec(v_pattern_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1519_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v_config_1489_; uint8_t v_trackZetaDelta_1490_; lean_object* v_zetaDeltaSet_1491_; lean_object* v_lctx_1492_; lean_object* v_localInstances_1493_; lean_object* v_defEqCtx_x3f_1494_; lean_object* v_synthPendingDepth_1495_; lean_object* v_customCanUnfoldPredicate_x3f_1496_; uint8_t v_univApprox_1497_; uint8_t v_inTypeClassResolution_1498_; uint8_t v_cacheInferType_1499_; uint64_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1488_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_1489_ = lean_ctor_get(v___x_1488_, 0);
v_trackZetaDelta_1490_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*7);
v_zetaDeltaSet_1491_ = lean_ctor_get(v___y_1462_, 1);
v_lctx_1492_ = lean_ctor_get(v___y_1462_, 2);
v_localInstances_1493_ = lean_ctor_get(v___y_1462_, 3);
v_defEqCtx_x3f_1494_ = lean_ctor_get(v___y_1462_, 4);
v_synthPendingDepth_1495_ = lean_ctor_get(v___y_1462_, 5);
v_customCanUnfoldPredicate_x3f_1496_ = lean_ctor_get(v___y_1462_, 6);
v_univApprox_1497_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1498_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*7 + 2);
v_cacheInferType_1499_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*7 + 3);
v___x_1500_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1489_);
lean_inc_ref(v_config_1489_);
v___x_1501_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1501_, 0, v_config_1489_);
lean_ctor_set_uint64(v___x_1501_, sizeof(void*)*1, v___x_1500_);
lean_inc(v_customCanUnfoldPredicate_x3f_1496_);
lean_inc(v_synthPendingDepth_1495_);
lean_inc(v_defEqCtx_x3f_1494_);
lean_inc_ref(v_localInstances_1493_);
lean_inc_ref(v_lctx_1492_);
lean_inc(v_zetaDeltaSet_1491_);
v___x_1502_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v_zetaDeltaSet_1491_);
lean_ctor_set(v___x_1502_, 2, v_lctx_1492_);
lean_ctor_set(v___x_1502_, 3, v_localInstances_1493_);
lean_ctor_set(v___x_1502_, 4, v_defEqCtx_x3f_1494_);
lean_ctor_set(v___x_1502_, 5, v_synthPendingDepth_1495_);
lean_ctor_set(v___x_1502_, 6, v_customCanUnfoldPredicate_x3f_1496_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*7, v_trackZetaDelta_1490_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*7 + 1, v_univApprox_1497_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1498_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*7 + 3, v_cacheInferType_1499_);
v___x_1503_ = l_Lean_Meta_DiscrTree_mkPath(v_lhs_1484_, v___x_1469_, v___x_1502_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec_ref_known(v___x_1502_, 7);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_a_1482_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
lean_dec_ref_known(v___x_1505_, 1);
v___x_1506_ = l_Lean_Meta_unificationHintExtension;
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v_declName_1460_);
lean_ctor_set(v___x_1486_, 0, v_a_1504_);
v___x_1508_ = v___x_1486_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_declName_1460_);
v___x_1508_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v___x_1506_, v___x_1508_, v_kind_1461_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1509_;
}
}
else
{
lean_dec(v_a_1504_);
lean_del_object(v___x_1486_);
lean_dec(v_declName_1460_);
return v___x_1505_;
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_del_object(v___x_1486_);
lean_dec(v_a_1482_);
lean_dec(v_declName_1460_);
v_a_1511_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1503_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1503_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_declName_1460_);
v_a_1521_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1475_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1475_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
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
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_declName_1460_);
v_a_1529_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1467_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1467_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object* v_declName_1537_, lean_object* v_kind_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
uint8_t v_kind_boxed_1544_; lean_object* v_res_1545_; 
v_kind_boxed_1544_ = lean_unbox(v_kind_1538_);
v_res_1545_ = l_Lean_Meta_addUnificationHint___lam__0(v_declName_1537_, v_kind_boxed_1544_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* v_declName_1546_, uint8_t v_kind_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1553_; lean_object* v___f_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1553_ = lean_box(v_kind_1547_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1554_, 0, v_declName_1546_);
lean_closure_set(v___f_1554_, 1, v___x_1553_);
v___x_1555_ = 0;
v___x_1556_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v___f_1554_, v___x_1555_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* v_declName_1557_, lean_object* v_kind_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
uint8_t v_kind_boxed_1564_; lean_object* v_res_1565_; 
v_kind_boxed_1564_ = lean_unbox(v_kind_1558_);
v_res_1565_ = l_Lean_Meta_addUnificationHint(v_declName_1557_, v_kind_boxed_1564_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object* v_00_u03b1_1566_, lean_object* v_00_u03b2_1567_, lean_object* v_00_u03c3_1568_, lean_object* v_ext_1569_, lean_object* v_b_1570_, uint8_t v_kind_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_1569_, v_b_1570_, v_kind_1571_, v___y_1573_, v___y_1574_, v___y_1575_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object* v_00_u03b1_1578_, lean_object* v_00_u03b2_1579_, lean_object* v_00_u03c3_1580_, lean_object* v_ext_1581_, lean_object* v_b_1582_, lean_object* v_kind_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v_kind_boxed_1589_; lean_object* v_res_1590_; 
v_kind_boxed_1589_ = lean_unbox(v_kind_1583_);
v_res_1590_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(v_00_u03b1_1578_, v_00_u03b2_1579_, v_00_u03c3_1580_, v_ext_1581_, v_b_1582_, v_kind_boxed_1589_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object* v_00_u03b1_1591_, lean_object* v_constName_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1599_, lean_object* v_constName_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(v_00_u03b1_1599_, v_constName_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2___redArg(){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2___redArg___boxed(lean_object* v___dummy_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2___redArg();
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2(lean_object* v_00_u03b2_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1615_, lean_object* v_ref_1616_, lean_object* v_constName_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___redArg(v_ref_1616_, v_constName_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1624_, lean_object* v_ref_1625_, lean_object* v_constName_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2(v_00_u03b1_1624_, v_ref_1625_, v_constName_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v_ref_1625_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_1633_, lean_object* v_ref_1634_, lean_object* v_msg_1635_, lean_object* v_declHint_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1634_, v_msg_1635_, v_declHint_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_ref_1644_, lean_object* v_msg_1645_, lean_object* v_declHint_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_1643_, v_ref_1644_, v_msg_1645_, v_declHint_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v_ref_1644_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8(lean_object* v_msg_1653_, lean_object* v_declHint_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg(v_msg_1653_, v_declHint_1654_, v___y_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_1661_, lean_object* v_declHint_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8(v_msg_1661_, v_declHint_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_00_u03b1_1669_, lean_object* v_ref_1670_, lean_object* v_msg_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_ref_1670_, v_msg_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b1_1678_, lean_object* v_ref_1679_, lean_object* v_msg_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__8(v_00_u03b1_1678_, v_ref_1679_, v_msg_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_ref_1679_);
return v_res_1686_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1693_; uint64_t v___x_1694_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1694_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1693_);
return v___x_1694_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1696_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1697_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set_uint64(v___x_1697_, sizeof(void*)*1, v___x_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
return v___x_1701_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
lean_ctor_set(v___x_1703_, 2, v___x_1702_);
lean_ctor_set(v___x_1703_, 3, v___x_1702_);
lean_ctor_set(v___x_1703_, 4, v___x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1704_, lean_object* v___x_1705_, lean_object* v_declName_1706_, lean_object* v_stx_1707_, uint8_t v_kind_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1707_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1712_) == 0)
{
uint8_t v___x_1713_; uint8_t v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_dec_ref_known(v___x_1712_, 1);
v___x_1713_ = 0;
v___x_1714_ = 1;
v___x_1715_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1716_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1717_ = lean_unsigned_to_nat(32u);
v___x_1718_ = lean_mk_empty_array_with_capacity(v___x_1717_);
v___x_1719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__2);
v___x_1720_ = ((size_t)5ULL);
lean_inc_n(v___x_1704_, 7);
v___x_1721_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1721_, 0, v___x_1719_);
lean_ctor_set(v___x_1721_, 1, v___x_1718_);
lean_ctor_set(v___x_1721_, 2, v___x_1704_);
lean_ctor_set(v___x_1721_, 3, v___x_1704_);
lean_ctor_set_usize(v___x_1721_, 4, v___x_1720_);
v___x_1722_ = lean_box(1);
lean_inc_ref(v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1716_);
lean_ctor_set(v___x_1723_, 1, v___x_1721_);
lean_ctor_set(v___x_1723_, 2, v___x_1722_);
v___x_1724_ = lean_mk_empty_array_with_capacity(v___x_1704_);
v___x_1725_ = lean_box(0);
lean_inc(v___x_1705_);
v___x_1726_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1726_, 0, v___x_1715_);
lean_ctor_set(v___x_1726_, 1, v___x_1705_);
lean_ctor_set(v___x_1726_, 2, v___x_1723_);
lean_ctor_set(v___x_1726_, 3, v___x_1724_);
lean_ctor_set(v___x_1726_, 4, v___x_1725_);
lean_ctor_set(v___x_1726_, 5, v___x_1704_);
lean_ctor_set(v___x_1726_, 6, v___x_1725_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*7, v___x_1713_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*7 + 1, v___x_1713_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*7 + 2, v___x_1713_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*7 + 3, v___x_1714_);
v___x_1727_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1704_);
lean_ctor_set(v___x_1727_, 1, v___x_1704_);
lean_ctor_set(v___x_1727_, 2, v___x_1704_);
lean_ctor_set(v___x_1727_, 3, v___x_1704_);
lean_ctor_set(v___x_1727_, 4, v___x_1716_);
lean_ctor_set(v___x_1727_, 5, v___x_1716_);
lean_ctor_set(v___x_1727_, 6, v___x_1716_);
lean_ctor_set(v___x_1727_, 7, v___x_1716_);
lean_ctor_set(v___x_1727_, 8, v___x_1716_);
lean_ctor_set(v___x_1727_, 9, v___x_1716_);
lean_ctor_set(v___x_1727_, 10, v___x_1716_);
v___x_1728_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
v___x_1729_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1716_);
lean_ctor_set(v___x_1730_, 1, v___x_1716_);
lean_ctor_set(v___x_1730_, 2, v___x_1704_);
v___x_1731_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1728_);
lean_ctor_set(v___x_1731_, 1, v___x_1716_);
lean_ctor_set(v___x_1731_, 2, v___x_1729_);
lean_ctor_set(v___x_1731_, 3, v___x_1716_);
lean_ctor_set(v___x_1731_, 4, v___x_1716_);
lean_ctor_set(v___x_1731_, 5, v___x_1716_);
lean_ctor_set(v___x_1731_, 6, v___x_1730_);
v___x_1732_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1727_);
lean_ctor_set(v___x_1733_, 1, v___x_1731_);
lean_ctor_set(v___x_1733_, 2, v___x_1705_);
lean_ctor_set(v___x_1733_, 3, v___x_1721_);
lean_ctor_set(v___x_1733_, 4, v___x_1732_);
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_st_mk_ref(v___x_1733_);
v___x_1736_ = l_Lean_Meta_addUnificationHint(v_declName_1706_, v_kind_1708_, v___x_1726_, v___x_1735_, v___y_1709_, v___y_1710_);
lean_dec_ref_known(v___x_1726_, 7);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1744_; 
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v___x_1736_, 0);
lean_dec(v_unused_1745_);
v___x_1738_ = v___x_1736_;
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
else
{
lean_dec(v___x_1736_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = lean_st_ref_get(v___x_1735_);
lean_dec(v___x_1735_);
lean_dec(v___x_1740_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1734_);
v___x_1742_ = v___x_1738_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1734_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
else
{
lean_dec(v___x_1735_);
return v___x_1736_;
}
}
else
{
lean_dec(v_declName_1706_);
lean_dec(v___x_1705_);
lean_dec(v___x_1704_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1746_, lean_object* v___x_1747_, lean_object* v_declName_1748_, lean_object* v_stx_1749_, lean_object* v_kind_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
uint8_t v_kind_boxed_1754_; lean_object* v_res_1755_; 
v_kind_boxed_1754_ = lean_unbox(v_kind_1750_);
v_res_1755_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1746_, v___x_1747_, v_declName_1748_, v_stx_1749_, v_kind_boxed_1754_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; lean_object* v_toCold_1761_; lean_object* v_env_1762_; lean_object* v_options_1763_; uint8_t v___x_1764_; lean_object* v_env_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1760_ = lean_st_ref_get(v___y_1758_);
v_toCold_1761_ = lean_ctor_get(v___y_1757_, 0);
v_env_1762_ = lean_ctor_get(v___x_1760_, 0);
lean_inc_ref(v_env_1762_);
lean_dec(v___x_1760_);
v_options_1763_ = lean_ctor_get(v_toCold_1761_, 2);
v___x_1764_ = 0;
v_env_1765_ = l_Lean_Environment_setRecordingDeps(v_env_1762_, v___x_1764_);
v___x_1766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_1767_ = lean_unsigned_to_nat(32u);
v___x_1768_ = lean_mk_empty_array_with_capacity(v___x_1767_);
lean_dec_ref(v___x_1768_);
v___x_1769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__2_spec__4_spec__7_spec__8___redArg___closed__4);
lean_inc_ref(v_options_1763_);
v___x_1770_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1770_, 0, v_env_1765_);
lean_ctor_set(v___x_1770_, 1, v___x_1766_);
lean_ctor_set(v___x_1770_, 2, v___x_1769_);
lean_ctor_set(v___x_1770_, 3, v_options_1763_);
v___x_1771_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v_msgData_1756_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_ref_1782_; lean_object* v___x_1783_; lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1792_; 
v_ref_1782_ = lean_ctor_get(v___y_1779_, 2);
v___x_1783_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msg_1778_, v___y_1779_, v___y_1780_);
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_inc(v_ref_1782_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_ref_1782_);
lean_ctor_set(v___x_1788_, 1, v_a_1784_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 1);
lean_ctor_set(v___x_1786_, 0, v___x_1788_);
v___x_1790_ = v___x_1786_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
return v_res_1797_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1804_, lean_object* v_decl_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1810_ = l_Lean_MessageData_ofName(v___x_1804_);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v___x_1813_, v___y_1806_, v___y_1807_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1815_, lean_object* v_decl_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1815_, v_decl_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v_decl_1816_);
return v_res_1820_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_unsigned_to_nat(3033092106u);
v___x_1865_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1866_ = l_Lean_Name_num___override(v___x_1865_, v___x_1864_);
return v___x_1866_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1869_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1870_ = l_Lean_Name_str___override(v___x_1869_, v___x_1868_);
return v___x_1870_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1873_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1874_ = l_Lean_Name_str___override(v___x_1873_, v___x_1872_);
return v___x_1874_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_unsigned_to_nat(2u);
v___x_1876_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1877_ = l_Lean_Name_num___override(v___x_1876_, v___x_1875_);
return v___x_1877_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1884_ = 0;
v___x_1885_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1886_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1887_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1888_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v___x_1886_);
lean_ctor_set(v___x_1888_, 2, v___x_1885_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3, v___x_1884_);
return v___x_1888_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___f_1889_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___f_1890_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1891_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v___f_1890_);
lean_ctor_set(v___x_1892_, 2, v___f_1889_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1895_ = l_Lean_registerBuiltinAttribute(v___x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1899_, v___y_1900_, v___y_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1904_, lean_object* v_msg_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(v_00_u03b1_1904_, v_msg_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints(lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v_ext_1914_; lean_object* v_toEnvExtension_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1913_ = l_Lean_Meta_unificationHintExtension;
v_ext_1914_ = lean_ctor_get(v___x_1913_, 1);
v_toEnvExtension_1915_ = lean_ctor_get(v_ext_1914_, 0);
v___x_1916_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
lean_inc_ref(v_toEnvExtension_1915_);
v___x_1917_ = l_Lean_recordExtGenAccess___redArg(v_toEnvExtension_1915_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1929_; 
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v___x_1917_, 0);
lean_dec(v_unused_1930_);
v___x_1919_ = v___x_1917_;
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
else
{
lean_dec(v___x_1917_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v_env_1922_; lean_object* v_asyncMode_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1921_ = lean_st_ref_get(v_a_1911_);
v_env_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc_ref(v_env_1922_);
lean_dec(v___x_1921_);
v_asyncMode_1923_ = lean_ctor_get(v_toEnvExtension_1915_, 2);
v___x_1924_ = 1;
v___x_1925_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1916_, v___x_1913_, v_env_1922_, v_asyncMode_1923_, v___x_1924_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1925_);
v___x_1927_ = v___x_1919_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_a_1931_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1917_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1917_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints___boxed(lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints(v_a_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* v_p_1943_, lean_object* v_e_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___y_1951_; lean_object* v___x_1968_; uint8_t v_transparency_1969_; uint8_t v___x_1970_; uint8_t v___x_1971_; 
v___x_1968_ = l_Lean_Meta_Context_config(v_a_1945_);
v_transparency_1969_ = lean_ctor_get_uint8(v___x_1968_, 9);
lean_dec_ref(v___x_1968_);
v___x_1970_ = 2;
v___x_1971_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1969_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v_keyedConfig_1972_; uint8_t v_trackZetaDelta_1973_; lean_object* v_zetaDeltaSet_1974_; lean_object* v_lctx_1975_; lean_object* v_localInstances_1976_; lean_object* v_defEqCtx_x3f_1977_; lean_object* v_synthPendingDepth_1978_; lean_object* v_customCanUnfoldPredicate_x3f_1979_; uint8_t v_univApprox_1980_; uint8_t v_inTypeClassResolution_1981_; uint8_t v_cacheInferType_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_keyedConfig_1972_ = lean_ctor_get(v_a_1945_, 0);
v_trackZetaDelta_1973_ = lean_ctor_get_uint8(v_a_1945_, sizeof(void*)*7);
v_zetaDeltaSet_1974_ = lean_ctor_get(v_a_1945_, 1);
v_lctx_1975_ = lean_ctor_get(v_a_1945_, 2);
v_localInstances_1976_ = lean_ctor_get(v_a_1945_, 3);
v_defEqCtx_x3f_1977_ = lean_ctor_get(v_a_1945_, 4);
v_synthPendingDepth_1978_ = lean_ctor_get(v_a_1945_, 5);
v_customCanUnfoldPredicate_x3f_1979_ = lean_ctor_get(v_a_1945_, 6);
v_univApprox_1980_ = lean_ctor_get_uint8(v_a_1945_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1981_ = lean_ctor_get_uint8(v_a_1945_, sizeof(void*)*7 + 2);
v_cacheInferType_1982_ = lean_ctor_get_uint8(v_a_1945_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1972_);
v___x_1983_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1970_, v_keyedConfig_1972_);
lean_inc(v_customCanUnfoldPredicate_x3f_1979_);
lean_inc(v_synthPendingDepth_1978_);
lean_inc(v_defEqCtx_x3f_1977_);
lean_inc_ref(v_localInstances_1976_);
lean_inc_ref(v_lctx_1975_);
lean_inc(v_zetaDeltaSet_1974_);
v___x_1984_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v_zetaDeltaSet_1974_);
lean_ctor_set(v___x_1984_, 2, v_lctx_1975_);
lean_ctor_set(v___x_1984_, 3, v_localInstances_1976_);
lean_ctor_set(v___x_1984_, 4, v_defEqCtx_x3f_1977_);
lean_ctor_set(v___x_1984_, 5, v_synthPendingDepth_1978_);
lean_ctor_set(v___x_1984_, 6, v_customCanUnfoldPredicate_x3f_1979_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*7, v_trackZetaDelta_1973_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*7 + 1, v_univApprox_1980_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1981_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*7 + 3, v_cacheInferType_1982_);
lean_inc(v_a_1948_);
lean_inc_ref(v_a_1947_);
lean_inc(v_a_1946_);
v___x_1985_ = lean_is_expr_def_eq(v_p_1943_, v_e_1944_, v___x_1984_, v_a_1946_, v_a_1947_, v_a_1948_);
v___y_1951_ = v___x_1985_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_1986_; 
lean_inc(v_a_1948_);
lean_inc_ref(v_a_1947_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
v___x_1986_ = lean_is_expr_def_eq(v_p_1943_, v_e_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
v___y_1951_ = v___x_1986_;
goto v___jp_1950_;
}
v___jp_1950_:
{
if (lean_obj_tag(v___y_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_a_1952_ = lean_ctor_get(v___y_1951_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___y_1951_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___y_1951_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___y_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
v_a_1960_ = lean_ctor_get(v___y_1951_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___y_1951_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___y_1951_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___y_1951_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object* v_p_1987_, lean_object* v_e_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_p_1987_, v_e_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = l_List_reverse___redArg(v_x_1996_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
return v___x_2003_;
}
else
{
lean_object* v_tail_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2022_; 
v_tail_2004_ = lean_ctor_get(v_x_1995_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_1995_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; 
v_unused_2023_ = lean_ctor_get(v_x_1995_, 0);
lean_dec(v_unused_2023_);
v___x_2006_ = v_x_1995_;
v_isShared_2007_ = v_isSharedCheck_2022_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_tail_2004_);
lean_dec(v_x_1995_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2022_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v_x_1996_);
lean_ctor_set(v___x_2006_, 0, v_a_2009_);
v___x_2011_ = v___x_2006_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2009_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_x_1996_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
v_x_1995_ = v_tail_2004_;
v_x_1996_ = v___x_2011_;
goto _start;
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_del_object(v___x_2006_);
lean_dec(v_tail_2004_);
lean_dec(v_x_1996_);
v_a_2014_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2008_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2008_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v_x_2024_, v_x_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2031_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2032_; double v___x_2033_; 
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_float_of_nat(v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object* v_cls_2037_, lean_object* v_msg_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_ref_2044_; lean_object* v___x_2045_; lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2091_; 
v_ref_2044_ = lean_ctor_get(v___y_2041_, 2);
v___x_2045_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2091_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2091_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v_traceState_2051_; lean_object* v_env_2052_; lean_object* v_nextMacroScope_2053_; lean_object* v_ngen_2054_; lean_object* v_auxDeclNGen_2055_; lean_object* v_cache_2056_; lean_object* v_recordedDeps_2057_; lean_object* v_messages_2058_; lean_object* v_infoState_2059_; lean_object* v_snapshotTasks_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2090_; 
v___x_2050_ = lean_st_ref_take(v___y_2042_);
v_traceState_2051_ = lean_ctor_get(v___x_2050_, 4);
v_env_2052_ = lean_ctor_get(v___x_2050_, 0);
v_nextMacroScope_2053_ = lean_ctor_get(v___x_2050_, 1);
v_ngen_2054_ = lean_ctor_get(v___x_2050_, 2);
v_auxDeclNGen_2055_ = lean_ctor_get(v___x_2050_, 3);
v_cache_2056_ = lean_ctor_get(v___x_2050_, 5);
v_recordedDeps_2057_ = lean_ctor_get(v___x_2050_, 6);
v_messages_2058_ = lean_ctor_get(v___x_2050_, 7);
v_infoState_2059_ = lean_ctor_get(v___x_2050_, 8);
v_snapshotTasks_2060_ = lean_ctor_get(v___x_2050_, 9);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2062_ = v___x_2050_;
v_isShared_2063_ = v_isSharedCheck_2090_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_snapshotTasks_2060_);
lean_inc(v_infoState_2059_);
lean_inc(v_messages_2058_);
lean_inc(v_recordedDeps_2057_);
lean_inc(v_cache_2056_);
lean_inc(v_traceState_2051_);
lean_inc(v_auxDeclNGen_2055_);
lean_inc(v_ngen_2054_);
lean_inc(v_nextMacroScope_2053_);
lean_inc(v_env_2052_);
lean_dec(v___x_2050_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2090_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
uint64_t v_tid_2064_; lean_object* v_traces_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2089_; 
v_tid_2064_ = lean_ctor_get_uint64(v_traceState_2051_, sizeof(void*)*1);
v_traces_2065_ = lean_ctor_get(v_traceState_2051_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_traceState_2051_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2067_ = v_traceState_2051_;
v_isShared_2068_ = v_isSharedCheck_2089_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_traces_2065_);
lean_dec(v_traceState_2051_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2089_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; double v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2069_ = lean_box(0);
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
v___x_2072_ = 0;
v___x_2073_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_2074_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2074_, 0, v_cls_2037_);
lean_ctor_set(v___x_2074_, 1, v___x_2070_);
lean_ctor_set(v___x_2074_, 2, v___x_2073_);
lean_ctor_set_float(v___x_2074_, sizeof(void*)*3, v___x_2071_);
lean_ctor_set_float(v___x_2074_, sizeof(void*)*3 + 8, v___x_2071_);
lean_ctor_set_uint8(v___x_2074_, sizeof(void*)*3 + 16, v___x_2072_);
v___x_2075_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2));
v___x_2076_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v_a_2046_);
lean_ctor_set(v___x_2076_, 2, v___x_2075_);
lean_inc(v_ref_2044_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v_ref_2044_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l_Lean_PersistentArray_push___redArg(v_traces_2065_, v___x_2077_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2078_);
v___x_2080_ = v___x_2067_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2078_);
lean_ctor_set_uint64(v_reuseFailAlloc_2088_, sizeof(void*)*1, v_tid_2064_);
v___x_2080_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2082_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 4, v___x_2080_);
v___x_2082_ = v___x_2062_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_env_2052_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_nextMacroScope_2053_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_ngen_2054_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_auxDeclNGen_2055_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2087_, 5, v_cache_2056_);
lean_ctor_set(v_reuseFailAlloc_2087_, 6, v_recordedDeps_2057_);
lean_ctor_set(v_reuseFailAlloc_2087_, 7, v_messages_2058_);
lean_ctor_set(v_reuseFailAlloc_2087_, 8, v_infoState_2059_);
lean_ctor_set(v_reuseFailAlloc_2087_, 9, v_snapshotTasks_2060_);
v___x_2082_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_st_ref_put(v___y_2042_, v___x_2082_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2069_);
v___x_2085_ = v___x_2048_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2069_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object* v_cls_2092_, lean_object* v_msg_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2092_, v_msg_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object* v_as_2103_, size_t v_sz_2104_, size_t v_i_2105_, lean_object* v_b_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_a_2113_; uint8_t v___x_2117_; 
v___x_2117_ = lean_usize_dec_lt(v_i_2105_, v_sz_2104_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_b_2106_);
return v___x_2118_;
}
else
{
lean_object* v_snd_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2209_; 
v_snd_2119_ = lean_ctor_get(v_b_2106_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_b_2106_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v_b_2106_, 0);
lean_dec(v_unused_2210_);
v___x_2121_ = v_b_2106_;
v_isShared_2122_ = v_isSharedCheck_2209_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_snd_2119_);
lean_dec(v_b_2106_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2209_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_array_2123_; lean_object* v_start_2124_; lean_object* v_stop_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_array_2123_ = lean_ctor_get(v_snd_2119_, 0);
v_start_2124_ = lean_ctor_get(v_snd_2119_, 1);
v_stop_2125_ = lean_ctor_get(v_snd_2119_, 2);
v___x_2126_ = lean_box(0);
v___x_2127_ = lean_nat_dec_lt(v_start_2124_, v_stop_2125_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2129_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2126_);
v___x_2129_ = v___x_2121_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_snd_2119_);
v___x_2129_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
return v___x_2130_;
}
}
else
{
lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2205_; 
lean_inc(v_stop_2125_);
lean_inc(v_start_2124_);
lean_inc_ref(v_array_2123_);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_snd_2119_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; lean_object* v_unused_2207_; lean_object* v_unused_2208_; 
v_unused_2206_ = lean_ctor_get(v_snd_2119_, 2);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_snd_2119_, 1);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_snd_2119_, 0);
lean_dec(v_unused_2208_);
v___x_2133_ = v_snd_2119_;
v_isShared_2134_ = v_isSharedCheck_2205_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v_snd_2119_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2205_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2135_ = lean_array_fget(v_array_2123_, v_start_2124_);
v___x_2136_ = lean_unsigned_to_nat(1u);
v___x_2137_ = lean_nat_add(v_start_2124_, v___x_2136_);
lean_dec(v_start_2124_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v___x_2137_);
v___x_2139_ = v___x_2133_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_array_2123_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_stop_2125_);
v___x_2139_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
uint8_t v___x_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; 
v___x_2140_ = 3;
v___x_2141_ = lean_unbox(v___x_2135_);
lean_dec(v___x_2135_);
v___x_2142_ = l_Lean_instBEqBinderInfo_beq(v___x_2141_, v___x_2140_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2144_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v___x_2139_);
lean_ctor_set(v___x_2121_, 0, v___x_2126_);
v___x_2144_ = v___x_2121_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
v_a_2113_ = v___x_2144_;
goto v___jp_2112_;
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2147_; 
v_a_2146_ = lean_array_uget_borrowed(v_as_2103_, v_i_2105_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
lean_inc(v_a_2146_);
v___x_2147_ = lean_infer_type(v_a_2146_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2149_ = l_Lean_Meta_trySynthInstance(v_a_2148_, v___x_2126_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2187_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2187_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2187_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
if (lean_obj_tag(v_a_2150_) == 1)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; 
lean_del_object(v___x_2152_);
v_a_2154_ = lean_ctor_get(v_a_2150_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v_a_2150_, 1);
lean_inc(v_a_2146_);
v___x_2155_ = l_Lean_Meta_isExprDefEq(v_a_2146_, v_a_2154_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2171_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2171_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2171_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
uint8_t v___x_2160_; 
v___x_2160_ = lean_unbox(v_a_2156_);
lean_dec(v_a_2156_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v___x_2139_);
lean_ctor_set(v___x_2121_, 0, v___x_2161_);
v___x_2163_ = v___x_2121_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2139_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2165_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2163_);
v___x_2165_ = v___x_2158_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v___x_2169_; 
lean_del_object(v___x_2158_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v___x_2139_);
lean_ctor_set(v___x_2121_, 0, v___x_2126_);
v___x_2169_ = v___x_2121_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2139_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
v_a_2113_ = v___x_2169_;
goto v___jp_2112_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v___x_2139_);
lean_del_object(v___x_2121_);
v_a_2172_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2155_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2155_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
lean_dec(v_a_2150_);
v___x_2180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v___x_2139_);
lean_ctor_set(v___x_2121_, 0, v___x_2180_);
v___x_2182_ = v___x_2121_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v___x_2139_);
v___x_2182_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2182_);
v___x_2184_ = v___x_2152_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v___x_2139_);
lean_del_object(v___x_2121_);
v_a_2188_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2149_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2149_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref(v___x_2139_);
lean_del_object(v___x_2121_);
v_a_2196_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2147_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2147_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
}
}
}
}
v___jp_2112_:
{
size_t v___x_2114_; size_t v___x_2115_; 
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2105_, v___x_2114_);
v_i_2105_ = v___x_2115_;
v_b_2106_ = v_a_2113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object* v_as_2211_, lean_object* v_sz_2212_, lean_object* v_i_2213_, lean_object* v_b_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
size_t v_sz_boxed_2220_; size_t v_i_boxed_2221_; lean_object* v_res_2222_; 
v_sz_boxed_2220_ = lean_unbox_usize(v_sz_2212_);
lean_dec(v_sz_2212_);
v_i_boxed_2221_ = lean_unbox_usize(v_i_2213_);
lean_dec(v_i_2213_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_as_2211_, v_sz_boxed_2220_, v_i_boxed_2221_, v_b_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec_ref(v_as_2211_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object* v_as_x27_2229_, lean_object* v_b_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
if (lean_obj_tag(v_as_x27_2229_) == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_b_2230_);
return v___x_2236_;
}
else
{
lean_object* v_head_2237_; lean_object* v_tail_2238_; lean_object* v_lhs_2239_; lean_object* v_rhs_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec_ref(v_b_2230_);
v_head_2237_ = lean_ctor_get(v_as_x27_2229_, 0);
v_tail_2238_ = lean_ctor_get(v_as_x27_2229_, 1);
v_lhs_2239_ = lean_ctor_get(v_head_2237_, 0);
v_rhs_2240_ = lean_ctor_get(v_head_2237_, 1);
v___x_2241_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
lean_inc(v___y_2234_);
lean_inc_ref(v___y_2233_);
lean_inc(v___y_2232_);
lean_inc_ref(v___y_2231_);
lean_inc_ref(v_rhs_2240_);
lean_inc_ref(v_lhs_2239_);
v___x_2242_ = lean_is_expr_def_eq(v_lhs_2239_, v_rhs_2240_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2253_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2253_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2253_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_unbox(v_a_2243_);
lean_dec(v_a_2243_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__1));
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2248_);
v___x_2250_ = v___x_2245_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
lean_del_object(v___x_2245_);
v_as_x27_2229_ = v_tail_2238_;
v_b_2230_ = v___x_2241_;
goto _start;
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
v_a_2254_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2242_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2242_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object* v_as_x27_2262_, lean_object* v_b_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2262_, v_b_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v_as_x27_2262_);
return v_res_2269_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7(void){
_start:
{
lean_object* v_cls_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_cls_2284_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2285_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6));
v___x_2286_ = l_Lean_Name_append(v___x_2285_, v_cls_2284_);
return v___x_2286_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8));
v___x_2289_ = l_Lean_stringToMessageData(v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object* v_candidate_2290_, lean_object* v_t_2291_, lean_object* v_s_2292_, uint8_t v_mayPostpone_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_cls_2299_; lean_object* v___x_2300_; 
v_cls_2299_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2300_ = l_Lean_Meta_saveState___redArg(v_a_2295_, v_a_2297_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2553_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2553_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2553_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_a_2306_; uint8_t v_a_2333_; lean_object* v___x_2345_; lean_object* v_cache_2346_; lean_object* v_mctx_2347_; lean_object* v_zetaDeltaFVarIds_2348_; lean_object* v_postponed_2349_; lean_object* v_diag_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2552_; 
v___x_2345_ = lean_st_ref_take(v_a_2295_);
v_cache_2346_ = lean_ctor_get(v___x_2345_, 1);
v_mctx_2347_ = lean_ctor_get(v___x_2345_, 0);
v_zetaDeltaFVarIds_2348_ = lean_ctor_get(v___x_2345_, 2);
v_postponed_2349_ = lean_ctor_get(v___x_2345_, 3);
v_diag_2350_ = lean_ctor_get(v___x_2345_, 4);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2352_ = v___x_2345_;
v_isShared_2353_ = v_isSharedCheck_2552_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_diag_2350_);
lean_inc(v_postponed_2349_);
lean_inc(v_zetaDeltaFVarIds_2348_);
lean_inc(v_cache_2346_);
lean_inc(v_mctx_2347_);
lean_dec(v___x_2345_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2552_;
goto v_resetjp_2351_;
}
v___jp_2305_:
{
uint8_t v___x_2307_; 
v___x_2307_ = l_Lean_Exception_isInterrupt(v_a_2306_);
if (v___x_2307_ == 0)
{
uint8_t v___x_2308_; 
lean_inc_ref(v_a_2306_);
v___x_2308_ = l_Lean_Exception_isRuntime(v_a_2306_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
lean_del_object(v___x_2303_);
v___x_2309_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2301_, v_a_2295_, v_a_2297_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v___x_2309_, 0);
lean_dec(v_unused_2317_);
v___x_2311_ = v___x_2309_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_dec(v___x_2309_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set_tag(v___x_2311_, 1);
lean_ctor_set(v___x_2311_, 0, v_a_2306_);
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2306_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_a_2306_);
v_a_2318_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2309_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2309_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_object* v___x_2327_; 
lean_dec(v_a_2301_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set_tag(v___x_2303_, 1);
lean_ctor_set(v___x_2303_, 0, v_a_2306_);
v___x_2327_ = v___x_2303_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2306_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_object* v___x_2330_; 
lean_dec(v_a_2301_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set_tag(v___x_2303_, 1);
lean_ctor_set(v___x_2303_, 0, v_a_2306_);
v___x_2330_ = v___x_2303_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2306_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
v___jp_2332_:
{
lean_object* v___x_2334_; 
lean_inc(v_a_2301_);
v___x_2334_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2301_, v_a_2295_, v_a_2297_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2342_; 
lean_del_object(v___x_2303_);
lean_dec(v_a_2301_);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v___x_2334_, 0);
lean_dec(v_unused_2343_);
v___x_2336_ = v___x_2334_;
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
else
{
lean_dec(v___x_2334_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2338_ = lean_box(v_a_2333_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2338_);
v___x_2340_ = v___x_2336_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2344_; 
v_a_2344_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2334_, 1);
v_a_2306_ = v_a_2344_;
goto v___jp_2305_;
}
}
v_resetjp_2351_:
{
lean_object* v_inferType_2354_; lean_object* v_funInfo_2355_; lean_object* v_synthInstance_2356_; lean_object* v_whnf_2357_; lean_object* v_defEqPerm_2358_; lean_object* v_unfold_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2550_; 
v_inferType_2354_ = lean_ctor_get(v_cache_2346_, 0);
v_funInfo_2355_ = lean_ctor_get(v_cache_2346_, 1);
v_synthInstance_2356_ = lean_ctor_get(v_cache_2346_, 2);
v_whnf_2357_ = lean_ctor_get(v_cache_2346_, 3);
v_defEqPerm_2358_ = lean_ctor_get(v_cache_2346_, 5);
v_unfold_2359_ = lean_ctor_get(v_cache_2346_, 6);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_cache_2346_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v_cache_2346_, 4);
lean_dec(v_unused_2551_);
v___x_2361_ = v_cache_2346_;
v_isShared_2362_ = v_isSharedCheck_2550_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_unfold_2359_);
lean_inc(v_defEqPerm_2358_);
lean_inc(v_whnf_2357_);
lean_inc(v_synthInstance_2356_);
lean_inc(v_funInfo_2355_);
lean_inc(v_inferType_2354_);
lean_dec(v_cache_2346_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2550_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2363_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 4, v___x_2363_);
v___x_2365_ = v___x_2361_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_inferType_2354_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_funInfo_2355_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_synthInstance_2356_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_whnf_2357_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2549_, 5, v_defEqPerm_2358_);
lean_ctor_set(v_reuseFailAlloc_2549_, 6, v_unfold_2359_);
v___x_2365_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 1, v___x_2365_);
v___x_2367_ = v___x_2352_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_mctx_2347_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_zetaDeltaFVarIds_2348_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_postponed_2349_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_diag_2350_);
v___x_2367_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_st_ref_put(v_a_2295_, v___x_2367_);
v___x_2369_ = l_Lean_Meta_getResetPostponed___redArg(v_a_2295_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; uint8_t v_a_2372_; uint8_t v_a_2415_; lean_object* v___x_2416_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2369_, 1);
lean_inc(v_candidate_2290_);
v___x_2416_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_candidate_2290_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v___x_2418_ = l_Lean_ConstantInfo_levelParams(v_a_2417_);
v___x_2419_ = lean_box(0);
v___x_2420_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v___x_2418_, v___x_2419_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2420_, 1);
v___x_2422_ = 0;
v___x_2423_ = l_Lean_Core_instantiateValueLevelParams(v_a_2417_, v_a_2421_, v___x_2422_, v_a_2296_, v_a_2297_);
lean_dec(v_a_2417_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v___x_2425_ = lean_box(0);
v___x_2426_ = l_Lean_Meta_lambdaMetaTelescope(v_a_2424_, v___x_2425_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
lean_dec(v_a_2424_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v_snd_2428_; lean_object* v_fst_2429_; lean_object* v_fst_2430_; lean_object* v_snd_2431_; lean_object* v___x_2432_; uint8_t v_foApprox_2433_; uint8_t v_ctxApprox_2434_; uint8_t v_quasiPatternApprox_2435_; uint8_t v_constApprox_2436_; uint8_t v_isDefEqStuckEx_2437_; uint8_t v_proofIrrelevance_2438_; uint8_t v_assignSyntheticOpaque_2439_; uint8_t v_offsetCnstrs_2440_; uint8_t v_transparency_2441_; uint8_t v_etaStruct_2442_; uint8_t v_univApprox_2443_; uint8_t v_iota_2444_; uint8_t v_beta_2445_; uint8_t v_proj_2446_; uint8_t v_zeta_2447_; uint8_t v_zetaDelta_2448_; uint8_t v_zetaUnused_2449_; uint8_t v_zetaHave_2450_; uint8_t v_canUnfoldPredicateConfig_2451_; uint8_t v_stringLitToCtor_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2535_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v_snd_2428_ = lean_ctor_get(v_a_2427_, 1);
lean_inc(v_snd_2428_);
v_fst_2429_ = lean_ctor_get(v_a_2427_, 0);
lean_inc(v_fst_2429_);
lean_dec(v_a_2427_);
v_fst_2430_ = lean_ctor_get(v_snd_2428_, 0);
lean_inc(v_fst_2430_);
v_snd_2431_ = lean_ctor_get(v_snd_2428_, 1);
lean_inc(v_snd_2431_);
lean_dec(v_snd_2428_);
v___x_2432_ = l_Lean_Meta_Context_config(v_a_2294_);
v_foApprox_2433_ = lean_ctor_get_uint8(v___x_2432_, 0);
v_ctxApprox_2434_ = lean_ctor_get_uint8(v___x_2432_, 1);
v_quasiPatternApprox_2435_ = lean_ctor_get_uint8(v___x_2432_, 2);
v_constApprox_2436_ = lean_ctor_get_uint8(v___x_2432_, 3);
v_isDefEqStuckEx_2437_ = lean_ctor_get_uint8(v___x_2432_, 4);
v_proofIrrelevance_2438_ = lean_ctor_get_uint8(v___x_2432_, 6);
v_assignSyntheticOpaque_2439_ = lean_ctor_get_uint8(v___x_2432_, 7);
v_offsetCnstrs_2440_ = lean_ctor_get_uint8(v___x_2432_, 8);
v_transparency_2441_ = lean_ctor_get_uint8(v___x_2432_, 9);
v_etaStruct_2442_ = lean_ctor_get_uint8(v___x_2432_, 10);
v_univApprox_2443_ = lean_ctor_get_uint8(v___x_2432_, 11);
v_iota_2444_ = lean_ctor_get_uint8(v___x_2432_, 12);
v_beta_2445_ = lean_ctor_get_uint8(v___x_2432_, 13);
v_proj_2446_ = lean_ctor_get_uint8(v___x_2432_, 14);
v_zeta_2447_ = lean_ctor_get_uint8(v___x_2432_, 15);
v_zetaDelta_2448_ = lean_ctor_get_uint8(v___x_2432_, 16);
v_zetaUnused_2449_ = lean_ctor_get_uint8(v___x_2432_, 17);
v_zetaHave_2450_ = lean_ctor_get_uint8(v___x_2432_, 18);
v_canUnfoldPredicateConfig_2451_ = lean_ctor_get_uint8(v___x_2432_, 19);
v_stringLitToCtor_2452_ = lean_ctor_get_uint8(v___x_2432_, 20);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2454_ = v___x_2432_;
v_isShared_2455_ = v_isSharedCheck_2535_;
goto v_resetjp_2453_;
}
else
{
lean_dec(v___x_2432_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2535_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; 
v___x_2456_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_2431_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_dec_ref_known(v___x_2456_, 1);
lean_del_object(v___x_2454_);
lean_dec(v_fst_2430_);
lean_dec(v_fst_2429_);
lean_dec(v_a_2370_);
lean_dec_ref(v_s_2292_);
lean_dec_ref(v_t_2291_);
lean_dec(v_candidate_2290_);
v_a_2333_ = v___x_2422_;
goto v___jp_2332_;
}
else
{
lean_object* v_a_2457_; lean_object* v_pattern_2458_; uint8_t v_trackZetaDelta_2459_; lean_object* v_zetaDeltaSet_2460_; lean_object* v_lctx_2461_; lean_object* v_localInstances_2462_; lean_object* v_defEqCtx_x3f_2463_; lean_object* v_synthPendingDepth_2464_; lean_object* v_customCanUnfoldPredicate_x3f_2465_; uint8_t v_univApprox_2466_; uint8_t v_inTypeClassResolution_2467_; uint8_t v_cacheInferType_2468_; lean_object* v_constraints_2469_; lean_object* v_lhs_2470_; lean_object* v_rhs_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2534_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v_pattern_2458_ = lean_ctor_get(v_a_2457_, 0);
lean_inc_ref(v_pattern_2458_);
v_trackZetaDelta_2459_ = lean_ctor_get_uint8(v_a_2294_, sizeof(void*)*7);
v_zetaDeltaSet_2460_ = lean_ctor_get(v_a_2294_, 1);
v_lctx_2461_ = lean_ctor_get(v_a_2294_, 2);
v_localInstances_2462_ = lean_ctor_get(v_a_2294_, 3);
v_defEqCtx_x3f_2463_ = lean_ctor_get(v_a_2294_, 4);
v_synthPendingDepth_2464_ = lean_ctor_get(v_a_2294_, 5);
v_customCanUnfoldPredicate_x3f_2465_ = lean_ctor_get(v_a_2294_, 6);
v_univApprox_2466_ = lean_ctor_get_uint8(v_a_2294_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2467_ = lean_ctor_get_uint8(v_a_2294_, sizeof(void*)*7 + 2);
v_cacheInferType_2468_ = lean_ctor_get_uint8(v_a_2294_, sizeof(void*)*7 + 3);
v_constraints_2469_ = lean_ctor_get(v_a_2457_, 1);
lean_inc(v_constraints_2469_);
lean_dec(v_a_2457_);
v_lhs_2470_ = lean_ctor_get(v_pattern_2458_, 0);
v_rhs_2471_ = lean_ctor_get(v_pattern_2458_, 1);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_pattern_2458_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2473_ = v_pattern_2458_;
v_isShared_2474_ = v_isSharedCheck_2534_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_rhs_2471_);
lean_inc(v_lhs_2470_);
lean_dec(v_pattern_2458_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2534_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2455_ == 0)
{
v___x_2476_ = v___x_2454_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 0, v_foApprox_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 1, v_ctxApprox_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 2, v_quasiPatternApprox_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 3, v_constApprox_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 4, v_isDefEqStuckEx_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 6, v_proofIrrelevance_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 7, v_assignSyntheticOpaque_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 8, v_offsetCnstrs_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 9, v_transparency_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 10, v_etaStruct_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 11, v_univApprox_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 12, v_iota_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 13, v_beta_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 14, v_proj_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 15, v_zeta_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 16, v_zetaDelta_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 17, v_zetaUnused_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 18, v_zetaHave_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 19, v_canUnfoldPredicateConfig_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 20, v_stringLitToCtor_2452_);
v___x_2476_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
uint64_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_ctor_set_uint8(v___x_2476_, 5, v___x_2422_);
v___x_2477_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2476_);
v___x_2478_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set_uint64(v___x_2478_, sizeof(void*)*1, v___x_2477_);
lean_inc(v_customCanUnfoldPredicate_x3f_2465_);
lean_inc(v_synthPendingDepth_2464_);
lean_inc(v_defEqCtx_x3f_2463_);
lean_inc_ref(v_localInstances_2462_);
lean_inc_ref(v_lctx_2461_);
lean_inc(v_zetaDeltaSet_2460_);
v___x_2479_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v_zetaDeltaSet_2460_);
lean_ctor_set(v___x_2479_, 2, v_lctx_2461_);
lean_ctor_set(v___x_2479_, 3, v_localInstances_2462_);
lean_ctor_set(v___x_2479_, 4, v_defEqCtx_x3f_2463_);
lean_ctor_set(v___x_2479_, 5, v_synthPendingDepth_2464_);
lean_ctor_set(v___x_2479_, 6, v_customCanUnfoldPredicate_x3f_2465_);
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*7, v_trackZetaDelta_2459_);
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*7 + 1, v_univApprox_2466_);
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2467_);
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*7 + 3, v_cacheInferType_2468_);
v___x_2480_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_lhs_2470_, v_t_2291_, v___x_2479_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; uint8_t v___x_2482_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
v___x_2482_ = lean_unbox(v_a_2481_);
lean_dec(v_a_2481_);
if (v___x_2482_ == 0)
{
lean_dec_ref_known(v___x_2479_, 7);
lean_del_object(v___x_2473_);
lean_dec_ref(v_rhs_2471_);
lean_dec(v_constraints_2469_);
lean_dec(v_fst_2430_);
lean_dec(v_fst_2429_);
lean_dec(v_a_2370_);
lean_dec_ref(v_s_2292_);
lean_dec(v_candidate_2290_);
v_a_2333_ = v___x_2422_;
goto v___jp_2332_;
}
else
{
lean_object* v___x_2483_; 
v___x_2483_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_rhs_2471_, v_s_2292_, v___x_2479_, v_a_2295_, v_a_2296_, v_a_2297_);
lean_dec_ref_known(v___x_2479_, 7);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; uint8_t v___x_2517_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v___x_2517_ = lean_unbox(v_a_2484_);
if (v___x_2517_ == 0)
{
lean_dec(v_a_2484_);
lean_del_object(v___x_2473_);
lean_dec(v_constraints_2469_);
lean_dec(v_fst_2430_);
lean_dec(v_fst_2429_);
lean_dec(v_a_2370_);
lean_dec(v_candidate_2290_);
v_a_2333_ = v___x_2422_;
goto v___jp_2332_;
}
else
{
lean_object* v_toCold_2518_; lean_object* v_options_2519_; uint8_t v_hasTrace_2520_; 
v_toCold_2518_ = lean_ctor_get(v_a_2296_, 0);
v_options_2519_ = lean_ctor_get(v_toCold_2518_, 2);
v_hasTrace_2520_ = lean_ctor_get_uint8(v_options_2519_, sizeof(void*)*1);
if (v_hasTrace_2520_ == 0)
{
lean_del_object(v___x_2473_);
lean_dec(v_candidate_2290_);
v___y_2486_ = v_a_2294_;
v___y_2487_ = v_a_2295_;
v___y_2488_ = v_a_2296_;
v___y_2489_ = v_a_2297_;
goto v___jp_2485_;
}
else
{
lean_object* v_inheritedTraceOptions_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_inheritedTraceOptions_2521_ = lean_ctor_get(v_toCold_2518_, 11);
v___x_2522_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7);
v___x_2523_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2521_, v_options_2519_, v___x_2522_);
if (v___x_2523_ == 0)
{
lean_del_object(v___x_2473_);
lean_dec(v_candidate_2290_);
v___y_2486_ = v_a_2294_;
v___y_2487_ = v_a_2295_;
v___y_2488_ = v_a_2296_;
v___y_2489_ = v_a_2297_;
goto v___jp_2485_;
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2524_ = l_Lean_MessageData_ofName(v_candidate_2290_);
v___x_2525_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9);
if (v_isShared_2474_ == 0)
{
lean_ctor_set_tag(v___x_2473_, 7);
lean_ctor_set(v___x_2473_, 1, v___x_2525_);
lean_ctor_set(v___x_2473_, 0, v___x_2524_);
v___x_2527_ = v___x_2473_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2299_, v___x_2527_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_dec_ref_known(v___x_2528_, 1);
v___y_2486_ = v_a_2294_;
v___y_2487_ = v_a_2295_;
v___y_2488_ = v_a_2296_;
v___y_2489_ = v_a_2297_;
goto v___jp_2485_;
}
else
{
lean_object* v_a_2529_; 
lean_dec(v_a_2484_);
lean_dec(v_constraints_2469_);
lean_dec(v_fst_2430_);
lean_dec(v_fst_2429_);
lean_dec(v_a_2370_);
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v_a_2306_ = v_a_2529_;
goto v___jp_2305_;
}
}
}
}
}
v___jp_2485_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4));
v___x_2491_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_constraints_2469_, v___x_2490_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v_constraints_2469_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v_fst_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2514_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v_fst_2493_ = lean_ctor_get(v_a_2492_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_a_2492_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; 
v_unused_2515_ = lean_ctor_get(v_a_2492_, 1);
lean_dec(v_unused_2515_);
v___x_2495_ = v_a_2492_;
v_isShared_2496_ = v_isSharedCheck_2514_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_fst_2493_);
lean_dec(v_a_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2514_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
if (lean_obj_tag(v_fst_2493_) == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2497_ = lean_unsigned_to_nat(0u);
v___x_2498_ = lean_array_get_size(v_fst_2430_);
v___x_2499_ = l_Array_toSubarray___redArg(v_fst_2430_, v___x_2497_, v___x_2498_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v___x_2499_);
lean_ctor_set(v___x_2495_, 0, v___x_2425_);
v___x_2501_ = v___x_2495_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
size_t v_sz_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v_sz_2502_ = lean_array_size(v_fst_2429_);
v___x_2503_ = ((size_t)0ULL);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_fst_2429_, v_sz_2502_, v___x_2503_, v___x_2501_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v_fst_2429_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v_fst_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v_fst_2506_ = lean_ctor_get(v_a_2505_, 0);
lean_inc(v_fst_2506_);
lean_dec(v_a_2505_);
if (lean_obj_tag(v_fst_2506_) == 0)
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_unbox(v_a_2484_);
lean_dec(v_a_2484_);
v_a_2372_ = v___x_2507_;
goto v___jp_2371_;
}
else
{
lean_object* v_val_2508_; uint8_t v___x_2509_; 
lean_dec(v_a_2484_);
v_val_2508_ = lean_ctor_get(v_fst_2506_, 0);
lean_inc(v_val_2508_);
lean_dec_ref_known(v_fst_2506_, 1);
v___x_2509_ = lean_unbox(v_val_2508_);
lean_dec(v_val_2508_);
v_a_2415_ = v___x_2509_;
goto v___jp_2414_;
}
}
else
{
lean_object* v_a_2510_; 
lean_dec(v_a_2484_);
lean_dec(v_a_2370_);
v_a_2510_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2510_);
lean_dec_ref_known(v___x_2504_, 1);
v_a_2306_ = v_a_2510_;
goto v___jp_2305_;
}
}
}
else
{
lean_object* v_val_2512_; uint8_t v___x_2513_; 
lean_del_object(v___x_2495_);
lean_dec(v_a_2484_);
lean_dec(v_fst_2430_);
lean_dec(v_fst_2429_);
v_val_2512_ = lean_ctor_get(v_fst_2493_, 0);
lean_inc(v_val_2512_);
lean_dec_ref_known(v_fst_2493_, 1);
v___x_2513_ = lean_unbox(v_val_2512_);
lean_dec(v_val_2512_);
v_a_2415_ = v___x_2513_;
goto v___jp_2414_;
}
}
}
else
{
lean_object* v_a_2516_; 
lean_dec(v_a_2484_);
lean_dec(v_fst_2430_);
lean_dec(v_fst_2429_);
lean_dec(v_a_2370_);
v_a_2516_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2491_, 1);
v_a_2306_ = v_a_2516_;
goto v___jp_2305_;
}
}
}
else
{
lean_object* v_a_2531_; 
lean_del_object(v___x_2473_);
lean_dec(v_constraints_2469_);
lean_dec(v_fst_2430_);
lean_dec(v_fst_2429_);
lean_dec(v_a_2370_);
lean_dec(v_candidate_2290_);
v_a_2531_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2483_, 1);
v_a_2306_ = v_a_2531_;
goto v___jp_2305_;
}
}
}
else
{
lean_object* v_a_2532_; 
lean_dec_ref_known(v___x_2479_, 7);
lean_del_object(v___x_2473_);
lean_dec_ref(v_rhs_2471_);
lean_dec(v_constraints_2469_);
lean_dec(v_fst_2430_);
lean_dec(v_fst_2429_);
lean_dec(v_a_2370_);
lean_dec_ref(v_s_2292_);
lean_dec(v_candidate_2290_);
v_a_2532_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2480_, 1);
v_a_2306_ = v_a_2532_;
goto v___jp_2305_;
}
}
}
}
}
}
else
{
lean_object* v_a_2536_; 
lean_dec(v_a_2370_);
lean_dec_ref(v_s_2292_);
lean_dec_ref(v_t_2291_);
lean_dec(v_candidate_2290_);
v_a_2536_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2426_, 1);
v_a_2306_ = v_a_2536_;
goto v___jp_2305_;
}
}
else
{
lean_object* v_a_2537_; 
lean_dec(v_a_2370_);
lean_dec_ref(v_s_2292_);
lean_dec_ref(v_t_2291_);
lean_dec(v_candidate_2290_);
v_a_2537_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2423_, 1);
v_a_2306_ = v_a_2537_;
goto v___jp_2305_;
}
}
else
{
lean_object* v_a_2538_; 
lean_dec(v_a_2417_);
lean_dec(v_a_2370_);
lean_dec_ref(v_s_2292_);
lean_dec_ref(v_t_2291_);
lean_dec(v_candidate_2290_);
v_a_2538_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2420_, 1);
v_a_2306_ = v_a_2538_;
goto v___jp_2305_;
}
}
else
{
lean_object* v_a_2539_; 
lean_dec(v_a_2370_);
lean_dec_ref(v_s_2292_);
lean_dec_ref(v_t_2291_);
lean_dec(v_candidate_2290_);
v_a_2539_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2416_, 1);
v_a_2306_ = v_a_2539_;
goto v___jp_2305_;
}
v___jp_2371_:
{
uint8_t v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = 0;
v___x_2374_ = l_Lean_Meta_processPostponed(v_mayPostpone_2293_, v___x_2373_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2412_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2412_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2412_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
uint8_t v___x_2379_; 
v___x_2379_ = lean_unbox(v_a_2375_);
lean_dec(v_a_2375_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_del_object(v___x_2377_);
lean_dec(v_a_2370_);
lean_inc(v_a_2301_);
v___x_2380_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2301_, v_a_2295_, v_a_2297_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2388_; 
lean_del_object(v___x_2303_);
lean_dec(v_a_2301_);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; 
v_unused_2389_ = lean_ctor_get(v___x_2380_, 0);
lean_dec(v_unused_2389_);
v___x_2382_ = v___x_2380_;
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
else
{
lean_dec(v___x_2380_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = lean_box(v___x_2373_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2384_);
v___x_2386_ = v___x_2382_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
else
{
lean_object* v_a_2390_; 
v_a_2390_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2380_, 1);
v_a_2306_ = v_a_2390_;
goto v___jp_2305_;
}
}
else
{
lean_object* v___x_2391_; lean_object* v_postponed_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_mctx_2395_; lean_object* v_cache_2396_; lean_object* v_zetaDeltaFVarIds_2397_; lean_object* v_diag_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2410_; 
lean_del_object(v___x_2303_);
lean_dec(v_a_2301_);
v___x_2391_ = lean_st_ref_get(v_a_2295_);
v_postponed_2392_ = lean_ctor_get(v___x_2391_, 3);
lean_inc_ref(v_postponed_2392_);
lean_dec(v___x_2391_);
v___x_2393_ = l_Lean_PersistentArray_append___redArg(v_a_2370_, v_postponed_2392_);
lean_dec_ref(v_postponed_2392_);
v___x_2394_ = lean_st_ref_take(v_a_2295_);
v_mctx_2395_ = lean_ctor_get(v___x_2394_, 0);
v_cache_2396_ = lean_ctor_get(v___x_2394_, 1);
v_zetaDeltaFVarIds_2397_ = lean_ctor_get(v___x_2394_, 2);
v_diag_2398_ = lean_ctor_get(v___x_2394_, 4);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v___x_2394_, 3);
lean_dec(v_unused_2411_);
v___x_2400_ = v___x_2394_;
v_isShared_2401_ = v_isSharedCheck_2410_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_diag_2398_);
lean_inc(v_zetaDeltaFVarIds_2397_);
lean_inc(v_cache_2396_);
lean_inc(v_mctx_2395_);
lean_dec(v___x_2394_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2410_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 3, v___x_2393_);
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_mctx_2395_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_cache_2396_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_zetaDeltaFVarIds_2397_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_diag_2398_);
v___x_2403_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v___x_2404_ = lean_st_ref_put(v_a_2295_, v___x_2403_);
v___x_2405_ = lean_box(v_a_2372_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2405_);
v___x_2407_ = v___x_2377_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
}
else
{
lean_object* v_a_2413_; 
lean_dec(v_a_2370_);
v_a_2413_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2374_, 1);
v_a_2306_ = v_a_2413_;
goto v___jp_2305_;
}
}
v___jp_2414_:
{
if (v_a_2415_ == 0)
{
lean_dec(v_a_2370_);
v_a_2333_ = v_a_2415_;
goto v___jp_2332_;
}
else
{
v_a_2372_ = v_a_2415_;
goto v___jp_2371_;
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_del_object(v___x_2303_);
lean_dec(v_a_2301_);
lean_dec_ref(v_s_2292_);
lean_dec_ref(v_t_2291_);
lean_dec(v_candidate_2290_);
v_a_2540_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2369_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2369_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
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
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_s_2292_);
lean_dec_ref(v_t_2291_);
lean_dec(v_candidate_2290_);
v_a_2554_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2300_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2300_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object* v_candidate_2562_, lean_object* v_t_2563_, lean_object* v_s_2564_, lean_object* v_mayPostpone_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
uint8_t v_mayPostpone_boxed_2571_; lean_object* v_res_2572_; 
v_mayPostpone_boxed_2571_ = lean_unbox(v_mayPostpone_2565_);
v_res_2572_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2562_, v_t_2563_, v_s_2564_, v_mayPostpone_boxed_2571_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
return v_res_2572_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_unsigned_to_nat(32u);
v___x_2574_ = lean_mk_empty_array_with_capacity(v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2576_ = ((size_t)5ULL);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = lean_unsigned_to_nat(32u);
v___x_2579_ = lean_mk_empty_array_with_capacity(v___x_2578_);
v___x_2580_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0);
v___x_2581_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v___x_2579_);
lean_ctor_set(v___x_2581_, 2, v___x_2577_);
lean_ctor_set(v___x_2581_, 3, v___x_2577_);
lean_ctor_set_usize(v___x_2581_, 4, v___x_2576_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; lean_object* v_traceState_2585_; lean_object* v_traces_2586_; lean_object* v___x_2587_; lean_object* v_traceState_2588_; lean_object* v_env_2589_; lean_object* v_nextMacroScope_2590_; lean_object* v_ngen_2591_; lean_object* v_auxDeclNGen_2592_; lean_object* v_cache_2593_; lean_object* v_recordedDeps_2594_; lean_object* v_messages_2595_; lean_object* v_infoState_2596_; lean_object* v_snapshotTasks_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2616_; 
v___x_2584_ = lean_st_ref_get(v___y_2582_);
v_traceState_2585_ = lean_ctor_get(v___x_2584_, 4);
lean_inc_ref(v_traceState_2585_);
lean_dec(v___x_2584_);
v_traces_2586_ = lean_ctor_get(v_traceState_2585_, 0);
lean_inc_ref(v_traces_2586_);
lean_dec_ref(v_traceState_2585_);
v___x_2587_ = lean_st_ref_take(v___y_2582_);
v_traceState_2588_ = lean_ctor_get(v___x_2587_, 4);
v_env_2589_ = lean_ctor_get(v___x_2587_, 0);
v_nextMacroScope_2590_ = lean_ctor_get(v___x_2587_, 1);
v_ngen_2591_ = lean_ctor_get(v___x_2587_, 2);
v_auxDeclNGen_2592_ = lean_ctor_get(v___x_2587_, 3);
v_cache_2593_ = lean_ctor_get(v___x_2587_, 5);
v_recordedDeps_2594_ = lean_ctor_get(v___x_2587_, 6);
v_messages_2595_ = lean_ctor_get(v___x_2587_, 7);
v_infoState_2596_ = lean_ctor_get(v___x_2587_, 8);
v_snapshotTasks_2597_ = lean_ctor_get(v___x_2587_, 9);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2599_ = v___x_2587_;
v_isShared_2600_ = v_isSharedCheck_2616_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_snapshotTasks_2597_);
lean_inc(v_infoState_2596_);
lean_inc(v_messages_2595_);
lean_inc(v_recordedDeps_2594_);
lean_inc(v_cache_2593_);
lean_inc(v_traceState_2588_);
lean_inc(v_auxDeclNGen_2592_);
lean_inc(v_ngen_2591_);
lean_inc(v_nextMacroScope_2590_);
lean_inc(v_env_2589_);
lean_dec(v___x_2587_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2616_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
uint64_t v_tid_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2614_; 
v_tid_2601_ = lean_ctor_get_uint64(v_traceState_2588_, sizeof(void*)*1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_traceState_2588_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v_traceState_2588_, 0);
lean_dec(v_unused_2615_);
v___x_2603_ = v_traceState_2588_;
v_isShared_2604_ = v_isSharedCheck_2614_;
goto v_resetjp_2602_;
}
else
{
lean_dec(v_traceState_2588_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2614_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2605_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2605_);
v___x_2607_ = v___x_2603_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2605_);
lean_ctor_set_uint64(v_reuseFailAlloc_2613_, sizeof(void*)*1, v_tid_2601_);
v___x_2607_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2609_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 4, v___x_2607_);
v___x_2609_ = v___x_2599_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_env_2589_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_nextMacroScope_2590_);
lean_ctor_set(v_reuseFailAlloc_2612_, 2, v_ngen_2591_);
lean_ctor_set(v_reuseFailAlloc_2612_, 3, v_auxDeclNGen_2592_);
lean_ctor_set(v_reuseFailAlloc_2612_, 4, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2612_, 5, v_cache_2593_);
lean_ctor_set(v_reuseFailAlloc_2612_, 6, v_recordedDeps_2594_);
lean_ctor_set(v_reuseFailAlloc_2612_, 7, v_messages_2595_);
lean_ctor_set(v_reuseFailAlloc_2612_, 8, v_infoState_2596_);
lean_ctor_set(v_reuseFailAlloc_2612_, 9, v_snapshotTasks_2597_);
v___x_2609_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_st_ref_put(v___y_2582_, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_traces_2586_);
return v___x_2611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___boxed(lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2617_);
lean_dec(v___y_2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2623_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
return v_res_2631_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object* v_opts_2632_, lean_object* v_opt_2633_){
_start:
{
lean_object* v_name_2634_; lean_object* v_defValue_2635_; lean_object* v_map_2636_; lean_object* v___x_2637_; 
v_name_2634_ = lean_ctor_get(v_opt_2633_, 0);
v_defValue_2635_ = lean_ctor_get(v_opt_2633_, 1);
v_map_2636_ = lean_ctor_get(v_opts_2632_, 0);
v___x_2637_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2636_, v_name_2634_);
if (lean_obj_tag(v___x_2637_) == 0)
{
uint8_t v___x_2638_; 
v___x_2638_ = lean_unbox(v_defValue_2635_);
return v___x_2638_;
}
else
{
lean_object* v_val_2639_; 
v_val_2639_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_val_2639_);
lean_dec_ref_known(v___x_2637_, 1);
if (lean_obj_tag(v_val_2639_) == 1)
{
uint8_t v_v_2640_; 
v_v_2640_ = lean_ctor_get_uint8(v_val_2639_, 0);
lean_dec_ref_known(v_val_2639_, 0);
return v_v_2640_;
}
else
{
uint8_t v___x_2641_; 
lean_dec(v_val_2639_);
v___x_2641_ = lean_unbox(v_defValue_2635_);
return v___x_2641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object* v_opts_2642_, lean_object* v_opt_2643_){
_start:
{
uint8_t v_res_2644_; lean_object* v_r_2645_; 
v_res_2644_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2642_, v_opt_2643_);
lean_dec_ref(v_opt_2643_);
lean_dec_ref(v_opts_2642_);
v_r_2645_ = lean_box(v_res_2644_);
return v_r_2645_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0));
v___x_2648_ = l_Lean_stringToMessageData(v___x_2647_);
return v___x_2648_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2));
v___x_2651_ = l_Lean_stringToMessageData(v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object* v_candidate_2655_, lean_object* v_t_2656_, lean_object* v_s_2657_, lean_object* v_x_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2664_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1);
v___x_2665_ = l_Lean_MessageData_ofName(v_candidate_2655_);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = l_Lean_MessageData_ofExpr(v_t_2656_);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = l_Lean_MessageData_ofExpr(v_s_2657_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object* v_candidate_2676_, lean_object* v_t_2677_, lean_object* v_s_2678_, lean_object* v_x_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(v_candidate_2676_, v_t_2677_, v_s_2678_, v_x_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec_ref(v_x_2679_);
return v_res_2685_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(lean_object* v_e_2686_){
_start:
{
if (lean_obj_tag(v_e_2686_) == 0)
{
uint8_t v___x_2687_; 
v___x_2687_ = 2;
return v___x_2687_;
}
else
{
lean_object* v_a_2688_; uint8_t v___x_2689_; 
v_a_2688_ = lean_ctor_get(v_e_2686_, 0);
v___x_2689_ = lean_unbox(v_a_2688_);
if (v___x_2689_ == 0)
{
uint8_t v___x_2690_; 
v___x_2690_ = 1;
return v___x_2690_;
}
else
{
uint8_t v___x_2691_; 
v___x_2691_ = 0;
return v___x_2691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(lean_object* v_e_2692_){
_start:
{
uint8_t v_res_2693_; lean_object* v_r_2694_; 
v_res_2693_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_e_2692_);
lean_dec_ref(v_e_2692_);
v_r_2694_ = lean_box(v_res_2693_);
return v_r_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(size_t v_sz_2695_, size_t v_i_2696_, lean_object* v_bs_2697_){
_start:
{
uint8_t v___x_2698_; 
v___x_2698_ = lean_usize_dec_lt(v_i_2696_, v_sz_2695_);
if (v___x_2698_ == 0)
{
return v_bs_2697_;
}
else
{
lean_object* v_v_2699_; lean_object* v_msg_2700_; lean_object* v___x_2701_; lean_object* v_bs_x27_2702_; size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
v_v_2699_ = lean_array_uget_borrowed(v_bs_2697_, v_i_2696_);
v_msg_2700_ = lean_ctor_get(v_v_2699_, 1);
lean_inc_ref(v_msg_2700_);
v___x_2701_ = lean_unsigned_to_nat(0u);
v_bs_x27_2702_ = lean_array_uset(v_bs_2697_, v_i_2696_, v___x_2701_);
v___x_2703_ = ((size_t)1ULL);
v___x_2704_ = lean_usize_add(v_i_2696_, v___x_2703_);
v___x_2705_ = lean_array_uset(v_bs_x27_2702_, v_i_2696_, v_msg_2700_);
v_i_2696_ = v___x_2704_;
v_bs_2697_ = v___x_2705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8___boxed(lean_object* v_sz_2707_, lean_object* v_i_2708_, lean_object* v_bs_2709_){
_start:
{
size_t v_sz_boxed_2710_; size_t v_i_boxed_2711_; lean_object* v_res_2712_; 
v_sz_boxed_2710_ = lean_unbox_usize(v_sz_2707_);
lean_dec(v_sz_2707_);
v_i_boxed_2711_ = lean_unbox_usize(v_i_2708_);
lean_dec(v_i_2708_);
v_res_2712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(v_sz_boxed_2710_, v_i_boxed_2711_, v_bs_2709_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(lean_object* v_oldTraces_2713_, lean_object* v_data_2714_, lean_object* v_ref_2715_, lean_object* v_msg_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_toCold_2722_; lean_object* v_currRecDepth_2723_; lean_object* v_ref_2724_; uint16_t v_optionFlags_2725_; uint8_t v_suppressElabErrors_2726_; uint8_t v_checkDeprecated_2727_; uint8_t v_isRecordingDeps_2728_; lean_object* v_ref_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_traceState_2732_; lean_object* v_traces_2733_; lean_object* v___x_2734_; size_t v_sz_2735_; size_t v___x_2736_; lean_object* v___x_2737_; lean_object* v_msg_2738_; lean_object* v___x_2739_; lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2778_; 
v_toCold_2722_ = lean_ctor_get(v___y_2719_, 0);
v_currRecDepth_2723_ = lean_ctor_get(v___y_2719_, 1);
v_ref_2724_ = lean_ctor_get(v___y_2719_, 2);
v_optionFlags_2725_ = lean_ctor_get_uint16(v___y_2719_, sizeof(void*)*3);
v_suppressElabErrors_2726_ = lean_ctor_get_uint8(v___y_2719_, sizeof(void*)*3 + 2);
v_checkDeprecated_2727_ = lean_ctor_get_uint8(v___y_2719_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2728_ = lean_ctor_get_uint8(v___y_2719_, sizeof(void*)*3 + 4);
v_ref_2729_ = l_Lean_replaceRef(v_ref_2715_, v_ref_2724_);
lean_inc(v_currRecDepth_2723_);
lean_inc_ref(v_toCold_2722_);
v___x_2730_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2730_, 0, v_toCold_2722_);
lean_ctor_set(v___x_2730_, 1, v_currRecDepth_2723_);
lean_ctor_set(v___x_2730_, 2, v_ref_2729_);
lean_ctor_set_uint16(v___x_2730_, sizeof(void*)*3, v_optionFlags_2725_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*3 + 2, v_suppressElabErrors_2726_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*3 + 3, v_checkDeprecated_2727_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*3 + 4, v_isRecordingDeps_2728_);
v___x_2731_ = lean_st_ref_get(v___y_2720_);
v_traceState_2732_ = lean_ctor_get(v___x_2731_, 4);
lean_inc_ref(v_traceState_2732_);
lean_dec(v___x_2731_);
v_traces_2733_ = lean_ctor_get(v_traceState_2732_, 0);
lean_inc_ref(v_traces_2733_);
lean_dec_ref(v_traceState_2732_);
v___x_2734_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2733_);
lean_dec_ref(v_traces_2733_);
v_sz_2735_ = lean_array_size(v___x_2734_);
v___x_2736_ = ((size_t)0ULL);
v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(v_sz_2735_, v___x_2736_, v___x_2734_);
v_msg_2738_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2738_, 0, v_data_2714_);
lean_ctor_set(v_msg_2738_, 1, v_msg_2716_);
lean_ctor_set(v_msg_2738_, 2, v___x_2737_);
v___x_2739_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2738_, v___y_2717_, v___y_2718_, v___x_2730_, v___y_2720_);
lean_dec_ref_known(v___x_2730_, 3);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2778_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2778_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; lean_object* v_traceState_2745_; lean_object* v_env_2746_; lean_object* v_nextMacroScope_2747_; lean_object* v_ngen_2748_; lean_object* v_auxDeclNGen_2749_; lean_object* v_cache_2750_; lean_object* v_recordedDeps_2751_; lean_object* v_messages_2752_; lean_object* v_infoState_2753_; lean_object* v_snapshotTasks_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2777_; 
v___x_2744_ = lean_st_ref_take(v___y_2720_);
v_traceState_2745_ = lean_ctor_get(v___x_2744_, 4);
v_env_2746_ = lean_ctor_get(v___x_2744_, 0);
v_nextMacroScope_2747_ = lean_ctor_get(v___x_2744_, 1);
v_ngen_2748_ = lean_ctor_get(v___x_2744_, 2);
v_auxDeclNGen_2749_ = lean_ctor_get(v___x_2744_, 3);
v_cache_2750_ = lean_ctor_get(v___x_2744_, 5);
v_recordedDeps_2751_ = lean_ctor_get(v___x_2744_, 6);
v_messages_2752_ = lean_ctor_get(v___x_2744_, 7);
v_infoState_2753_ = lean_ctor_get(v___x_2744_, 8);
v_snapshotTasks_2754_ = lean_ctor_get(v___x_2744_, 9);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2756_ = v___x_2744_;
v_isShared_2757_ = v_isSharedCheck_2777_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_snapshotTasks_2754_);
lean_inc(v_infoState_2753_);
lean_inc(v_messages_2752_);
lean_inc(v_recordedDeps_2751_);
lean_inc(v_cache_2750_);
lean_inc(v_traceState_2745_);
lean_inc(v_auxDeclNGen_2749_);
lean_inc(v_ngen_2748_);
lean_inc(v_nextMacroScope_2747_);
lean_inc(v_env_2746_);
lean_dec(v___x_2744_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2777_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
uint64_t v_tid_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2775_; 
v_tid_2758_ = lean_ctor_get_uint64(v_traceState_2745_, sizeof(void*)*1);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_traceState_2745_);
if (v_isSharedCheck_2775_ == 0)
{
lean_object* v_unused_2776_; 
v_unused_2776_ = lean_ctor_get(v_traceState_2745_, 0);
lean_dec(v_unused_2776_);
v___x_2760_ = v_traceState_2745_;
v_isShared_2761_ = v_isSharedCheck_2775_;
goto v_resetjp_2759_;
}
else
{
lean_dec(v_traceState_2745_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2775_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_ref_2715_);
lean_ctor_set(v___x_2763_, 1, v_a_2740_);
v___x_2764_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2713_, v___x_2763_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2764_);
v___x_2766_ = v___x_2760_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2764_);
lean_ctor_set_uint64(v_reuseFailAlloc_2774_, sizeof(void*)*1, v_tid_2758_);
v___x_2766_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2768_; 
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 4, v___x_2766_);
v___x_2768_ = v___x_2756_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_env_2746_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_nextMacroScope_2747_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_ngen_2748_);
lean_ctor_set(v_reuseFailAlloc_2773_, 3, v_auxDeclNGen_2749_);
lean_ctor_set(v_reuseFailAlloc_2773_, 4, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2773_, 5, v_cache_2750_);
lean_ctor_set(v_reuseFailAlloc_2773_, 6, v_recordedDeps_2751_);
lean_ctor_set(v_reuseFailAlloc_2773_, 7, v_messages_2752_);
lean_ctor_set(v_reuseFailAlloc_2773_, 8, v_infoState_2753_);
lean_ctor_set(v_reuseFailAlloc_2773_, 9, v_snapshotTasks_2754_);
v___x_2768_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2769_ = lean_st_ref_put(v___y_2720_, v___x_2768_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2762_);
v___x_2771_ = v___x_2742_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2762_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(lean_object* v_oldTraces_2779_, lean_object* v_data_2780_, lean_object* v_ref_2781_, lean_object* v_msg_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_oldTraces_2779_, v_data_2780_, v_ref_2781_, v_msg_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(lean_object* v_opts_2789_, lean_object* v_opt_2790_){
_start:
{
lean_object* v_name_2791_; lean_object* v_defValue_2792_; lean_object* v_map_2793_; lean_object* v___x_2794_; 
v_name_2791_ = lean_ctor_get(v_opt_2790_, 0);
v_defValue_2792_ = lean_ctor_get(v_opt_2790_, 1);
v_map_2793_ = lean_ctor_get(v_opts_2789_, 0);
v___x_2794_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2793_, v_name_2791_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_inc(v_defValue_2792_);
return v_defValue_2792_;
}
else
{
lean_object* v_val_2795_; 
v_val_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_val_2795_);
lean_dec_ref_known(v___x_2794_, 1);
if (lean_obj_tag(v_val_2795_) == 3)
{
lean_object* v_v_2796_; 
v_v_2796_ = lean_ctor_get(v_val_2795_, 0);
lean_inc(v_v_2796_);
lean_dec_ref_known(v_val_2795_, 1);
return v_v_2796_;
}
else
{
lean_dec(v_val_2795_);
lean_inc(v_defValue_2792_);
return v_defValue_2792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(lean_object* v_opts_2797_, lean_object* v_opt_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2797_, v_opt_2798_);
lean_dec_ref(v_opt_2798_);
lean_dec_ref(v_opts_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(lean_object* v_x_2800_){
_start:
{
if (lean_obj_tag(v_x_2800_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
v_a_2802_ = lean_ctor_get(v_x_2800_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_x_2800_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v_x_2800_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v_x_2800_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set_tag(v___x_2804_, 1);
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
v_a_2810_ = lean_ctor_get(v_x_2800_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_x_2800_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v_x_2800_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v_x_2800_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set_tag(v___x_2812_, 0);
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg___boxed(lean_object* v_x_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_x_2818_);
return v_res_2820_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0));
v___x_2823_ = l_Lean_stringToMessageData(v___x_2822_);
return v___x_2823_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2(void){
_start:
{
lean_object* v___x_2824_; double v___x_2825_; 
v___x_2824_ = lean_unsigned_to_nat(1000u);
v___x_2825_ = lean_float_of_nat(v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object* v_cls_2826_, uint8_t v_collapsed_2827_, lean_object* v_tag_2828_, lean_object* v_opts_2829_, uint8_t v_clsEnabled_2830_, lean_object* v_oldTraces_2831_, lean_object* v_msg_2832_, lean_object* v_resStartStop_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_fst_2839_; lean_object* v_snd_2840_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v_data_2844_; lean_object* v_fst_2855_; lean_object* v_snd_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; lean_object* v___y_2860_; lean_object* v_a_2861_; uint8_t v___y_2876_; double v___y_2908_; 
v_fst_2839_ = lean_ctor_get(v_resStartStop_2833_, 0);
lean_inc(v_fst_2839_);
v_snd_2840_ = lean_ctor_get(v_resStartStop_2833_, 1);
lean_inc(v_snd_2840_);
lean_dec_ref(v_resStartStop_2833_);
v_fst_2855_ = lean_ctor_get(v_snd_2840_, 0);
lean_inc(v_fst_2855_);
v_snd_2856_ = lean_ctor_get(v_snd_2840_, 1);
lean_inc(v_snd_2856_);
lean_dec(v_snd_2840_);
v___x_2857_ = l_Lean_trace_profiler;
v___x_2858_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2829_, v___x_2857_);
if (v___x_2858_ == 0)
{
v___y_2876_ = v___x_2858_;
goto v___jp_2875_;
}
else
{
lean_object* v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2914_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2829_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v___x_2916_; double v___x_2917_; double v___x_2918_; double v___x_2919_; 
v___x_2915_ = l_Lean_trace_profiler_threshold;
v___x_2916_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2829_, v___x_2915_);
v___x_2917_ = lean_float_of_nat(v___x_2916_);
v___x_2918_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2);
v___x_2919_ = lean_float_div(v___x_2917_, v___x_2918_);
v___y_2908_ = v___x_2919_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; double v___x_2922_; 
v___x_2920_ = l_Lean_trace_profiler_threshold;
v___x_2921_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2829_, v___x_2920_);
v___x_2922_ = lean_float_of_nat(v___x_2921_);
v___y_2908_ = v___x_2922_;
goto v___jp_2907_;
}
}
v___jp_2841_:
{
lean_object* v___x_2845_; 
lean_inc(v___y_2842_);
v___x_2845_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_oldTraces_2831_, v_data_2844_, v___y_2842_, v___y_2843_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v___x_2846_; 
lean_dec_ref_known(v___x_2845_, 1);
v___x_2846_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_fst_2839_);
return v___x_2846_;
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_fst_2839_);
v_a_2847_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2845_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2845_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
v___jp_2859_:
{
uint8_t v_result_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; double v___x_2865_; lean_object* v_data_2866_; 
v_result_2862_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_fst_2839_);
v___x_2863_ = lean_box(v_result_2862_);
v___x_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
v___x_2865_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
lean_inc_ref(v_tag_2828_);
lean_inc_ref(v___x_2864_);
lean_inc(v_cls_2826_);
v_data_2866_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2866_, 0, v_cls_2826_);
lean_ctor_set(v_data_2866_, 1, v___x_2864_);
lean_ctor_set(v_data_2866_, 2, v_tag_2828_);
lean_ctor_set_float(v_data_2866_, sizeof(void*)*3, v___x_2865_);
lean_ctor_set_float(v_data_2866_, sizeof(void*)*3 + 8, v___x_2865_);
lean_ctor_set_uint8(v_data_2866_, sizeof(void*)*3 + 16, v_collapsed_2827_);
if (v___x_2858_ == 0)
{
lean_dec_ref_known(v___x_2864_, 1);
lean_dec(v_snd_2856_);
lean_dec(v_fst_2855_);
lean_dec_ref(v_tag_2828_);
lean_dec(v_cls_2826_);
v___y_2842_ = v___y_2860_;
v___y_2843_ = v_a_2861_;
v_data_2844_ = v_data_2866_;
goto v___jp_2841_;
}
else
{
lean_object* v_data_2867_; double v___x_2868_; double v___x_2869_; 
lean_dec_ref_known(v_data_2866_, 3);
v_data_2867_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2867_, 0, v_cls_2826_);
lean_ctor_set(v_data_2867_, 1, v___x_2864_);
lean_ctor_set(v_data_2867_, 2, v_tag_2828_);
v___x_2868_ = lean_unbox_float(v_fst_2855_);
lean_dec(v_fst_2855_);
lean_ctor_set_float(v_data_2867_, sizeof(void*)*3, v___x_2868_);
v___x_2869_ = lean_unbox_float(v_snd_2856_);
lean_dec(v_snd_2856_);
lean_ctor_set_float(v_data_2867_, sizeof(void*)*3 + 8, v___x_2869_);
lean_ctor_set_uint8(v_data_2867_, sizeof(void*)*3 + 16, v_collapsed_2827_);
v___y_2842_ = v___y_2860_;
v___y_2843_ = v_a_2861_;
v_data_2844_ = v_data_2867_;
goto v___jp_2841_;
}
}
v___jp_2870_:
{
lean_object* v_ref_2871_; lean_object* v___x_2872_; 
v_ref_2871_ = lean_ctor_get(v___y_2836_, 2);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc(v_fst_2839_);
v___x_2872_ = lean_apply_6(v_msg_2832_, v_fst_2839_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, lean_box(0));
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___y_2860_ = v_ref_2871_;
v_a_2861_ = v_a_2873_;
goto v___jp_2859_;
}
else
{
lean_object* v___x_2874_; 
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1);
v___y_2860_ = v_ref_2871_;
v_a_2861_ = v___x_2874_;
goto v___jp_2859_;
}
}
v___jp_2875_:
{
if (v_clsEnabled_2830_ == 0)
{
if (v___y_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v_traceState_2878_; lean_object* v_env_2879_; lean_object* v_nextMacroScope_2880_; lean_object* v_ngen_2881_; lean_object* v_auxDeclNGen_2882_; lean_object* v_cache_2883_; lean_object* v_recordedDeps_2884_; lean_object* v_messages_2885_; lean_object* v_infoState_2886_; lean_object* v_snapshotTasks_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_snd_2856_);
lean_dec(v_fst_2855_);
lean_dec_ref(v_msg_2832_);
lean_dec_ref(v_tag_2828_);
lean_dec(v_cls_2826_);
v___x_2877_ = lean_st_ref_take(v___y_2837_);
v_traceState_2878_ = lean_ctor_get(v___x_2877_, 4);
v_env_2879_ = lean_ctor_get(v___x_2877_, 0);
v_nextMacroScope_2880_ = lean_ctor_get(v___x_2877_, 1);
v_ngen_2881_ = lean_ctor_get(v___x_2877_, 2);
v_auxDeclNGen_2882_ = lean_ctor_get(v___x_2877_, 3);
v_cache_2883_ = lean_ctor_get(v___x_2877_, 5);
v_recordedDeps_2884_ = lean_ctor_get(v___x_2877_, 6);
v_messages_2885_ = lean_ctor_get(v___x_2877_, 7);
v_infoState_2886_ = lean_ctor_get(v___x_2877_, 8);
v_snapshotTasks_2887_ = lean_ctor_get(v___x_2877_, 9);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2889_ = v___x_2877_;
v_isShared_2890_ = v_isSharedCheck_2906_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_snapshotTasks_2887_);
lean_inc(v_infoState_2886_);
lean_inc(v_messages_2885_);
lean_inc(v_recordedDeps_2884_);
lean_inc(v_cache_2883_);
lean_inc(v_traceState_2878_);
lean_inc(v_auxDeclNGen_2882_);
lean_inc(v_ngen_2881_);
lean_inc(v_nextMacroScope_2880_);
lean_inc(v_env_2879_);
lean_dec(v___x_2877_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2906_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
uint64_t v_tid_2891_; lean_object* v_traces_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2905_; 
v_tid_2891_ = lean_ctor_get_uint64(v_traceState_2878_, sizeof(void*)*1);
v_traces_2892_ = lean_ctor_get(v_traceState_2878_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_traceState_2878_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2894_ = v_traceState_2878_;
v_isShared_2895_ = v_isSharedCheck_2905_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_traces_2892_);
lean_dec(v_traceState_2878_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2905_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2831_, v_traces_2892_);
lean_dec_ref(v_traces_2892_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2896_);
v___x_2898_ = v___x_2894_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2896_);
lean_ctor_set_uint64(v_reuseFailAlloc_2904_, sizeof(void*)*1, v_tid_2891_);
v___x_2898_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2900_; 
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 4, v___x_2898_);
v___x_2900_ = v___x_2889_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_env_2879_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_nextMacroScope_2880_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_ngen_2881_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_auxDeclNGen_2882_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_cache_2883_);
lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_recordedDeps_2884_);
lean_ctor_set(v_reuseFailAlloc_2903_, 7, v_messages_2885_);
lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_infoState_2886_);
lean_ctor_set(v_reuseFailAlloc_2903_, 9, v_snapshotTasks_2887_);
v___x_2900_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_st_ref_put(v___y_2837_, v___x_2900_);
v___x_2902_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_fst_2839_);
return v___x_2902_;
}
}
}
}
}
else
{
goto v___jp_2870_;
}
}
else
{
goto v___jp_2870_;
}
}
v___jp_2907_:
{
double v___x_2909_; double v___x_2910_; double v___x_2911_; uint8_t v___x_2912_; 
v___x_2909_ = lean_unbox_float(v_snd_2856_);
v___x_2910_ = lean_unbox_float(v_fst_2855_);
v___x_2911_ = lean_float_sub(v___x_2909_, v___x_2910_);
v___x_2912_ = lean_float_decLt(v___y_2908_, v___x_2911_);
v___y_2876_ = v___x_2912_;
goto v___jp_2875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object* v_cls_2923_, lean_object* v_collapsed_2924_, lean_object* v_tag_2925_, lean_object* v_opts_2926_, lean_object* v_clsEnabled_2927_, lean_object* v_oldTraces_2928_, lean_object* v_msg_2929_, lean_object* v_resStartStop_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_collapsed_boxed_2936_; uint8_t v_clsEnabled_boxed_2937_; lean_object* v_res_2938_; 
v_collapsed_boxed_2936_ = lean_unbox(v_collapsed_2924_);
v_clsEnabled_boxed_2937_ = lean_unbox(v_clsEnabled_2927_);
v_res_2938_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2923_, v_collapsed_boxed_2936_, v_tag_2925_, v_opts_2926_, v_clsEnabled_boxed_2937_, v_oldTraces_2928_, v_msg_2929_, v_resStartStop_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v_opts_2926_);
return v_res_2938_;
}
}
static double _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0(void){
_start:
{
lean_object* v___x_2939_; double v___x_2940_; 
v___x_2939_ = lean_unsigned_to_nat(1000000000u);
v___x_2940_ = lean_float_of_nat(v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object* v_t_2941_, lean_object* v_s_2942_, lean_object* v_candidate_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_toCold_2949_; lean_object* v_options_2950_; lean_object* v_inheritedTraceOptions_2951_; uint8_t v_hasTrace_2952_; uint8_t v___x_2953_; 
v_toCold_2949_ = lean_ctor_get(v_a_2946_, 0);
v_options_2950_ = lean_ctor_get(v_toCold_2949_, 2);
v_inheritedTraceOptions_2951_ = lean_ctor_get(v_toCold_2949_, 11);
v_hasTrace_2952_ = lean_ctor_get_uint8(v_options_2950_, sizeof(void*)*1);
v___x_2953_ = 1;
if (v_hasTrace_2952_ == 0)
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2943_, v_t_2941_, v_s_2942_, v___x_2953_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_2954_;
}
else
{
lean_object* v___f_2955_; lean_object* v_cls_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v_a_2963_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v_a_2978_; 
lean_inc_ref(v_s_2942_);
lean_inc_ref(v_t_2941_);
lean_inc(v_candidate_2943_);
v___f_2955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2955_, 0, v_candidate_2943_);
lean_closure_set(v___f_2955_, 1, v_t_2941_);
lean_closure_set(v___f_2955_, 2, v_s_2942_);
v_cls_2956_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2957_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_2958_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7);
v___x_2959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2951_, v_options_2950_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___x_3028_ = l_Lean_trace_profiler;
v___x_3029_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2950_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
lean_dec_ref(v___f_2955_);
v___x_3030_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2943_, v_t_2941_, v_s_2942_, v___x_2953_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_3030_;
}
else
{
goto v___jp_2987_;
}
}
else
{
goto v___jp_2987_;
}
v___jp_2960_:
{
lean_object* v___x_2964_; double v___x_2965_; double v___x_2966_; double v___x_2967_; double v___x_2968_; double v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2964_ = lean_io_mono_nanos_now();
v___x_2965_ = lean_float_of_nat(v___y_2961_);
v___x_2966_ = lean_float_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0);
v___x_2967_ = lean_float_div(v___x_2965_, v___x_2966_);
v___x_2968_ = lean_float_of_nat(v___x_2964_);
v___x_2969_ = lean_float_div(v___x_2968_, v___x_2966_);
v___x_2970_ = lean_box_float(v___x_2967_);
v___x_2971_ = lean_box_float(v___x_2969_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v_a_2963_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2956_, v___x_2953_, v___x_2957_, v_options_2950_, v___x_2959_, v___y_2962_, v___f_2955_, v___x_2973_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_2974_;
}
v___jp_2975_:
{
lean_object* v___x_2979_; double v___x_2980_; double v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2979_ = lean_io_get_num_heartbeats();
v___x_2980_ = lean_float_of_nat(v___y_2977_);
v___x_2981_ = lean_float_of_nat(v___x_2979_);
v___x_2982_ = lean_box_float(v___x_2980_);
v___x_2983_ = lean_box_float(v___x_2981_);
v___x_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v_a_2978_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2956_, v___x_2953_, v___x_2957_, v_options_2950_, v___x_2959_, v___y_2976_, v___f_2955_, v___x_2985_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_2986_;
}
v___jp_2987_:
{
lean_object* v___x_2988_; lean_object* v_a_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2988_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v_a_2947_);
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref(v___x_2988_);
v___x_2990_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2991_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2950_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_io_mono_nanos_now();
v___x_2993_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2943_, v_t_2941_, v_s_2942_, v___x_2953_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set_tag(v___x_2996_, 1);
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
v___y_2961_ = v___x_2992_;
v___y_2962_ = v_a_2989_;
v_a_2963_ = v___x_2999_;
goto v___jp_2960_;
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
v_a_3002_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2993_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2993_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
lean_ctor_set_tag(v___x_3004_, 0);
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
v___y_2961_ = v___x_2992_;
v___y_2962_ = v_a_2989_;
v_a_2963_ = v___x_3007_;
goto v___jp_2960_;
}
}
}
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_io_get_num_heartbeats();
v___x_3011_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2943_, v_t_2941_, v_s_2942_, v___x_2953_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 1);
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
v___y_2976_ = v_a_2989_;
v___y_2977_ = v___x_3010_;
v_a_2978_ = v___x_3017_;
goto v___jp_2975_;
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
v_a_3020_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3011_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3011_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set_tag(v___x_3022_, 0);
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
v___y_2976_ = v_a_2989_;
v___y_2977_ = v___x_3010_;
v_a_2978_ = v___x_3025_;
goto v___jp_2975_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object* v_t_3031_, lean_object* v_s_3032_, lean_object* v_candidate_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_3031_, v_s_3032_, v_candidate_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object* v_as_3040_, lean_object* v_as_x27_3041_, lean_object* v_b_3042_, lean_object* v_a_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_3041_, v_b_3042_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object* v_as_3050_, lean_object* v_as_x27_3051_, lean_object* v_b_3052_, lean_object* v_a_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(v_as_3050_, v_as_x27_3051_, v_b_3052_, v_a_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v_as_x27_3051_);
lean_dec(v_as_3050_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(lean_object* v_00_u03b1_3060_, lean_object* v_x_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_x_3061_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(lean_object* v_00_u03b1_3068_, lean_object* v_x_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_00_u03b1_3068_, v_x_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(lean_object* v_t_3076_, lean_object* v_s_3077_, uint8_t v___x_3078_, lean_object* v_as_3079_, size_t v_sz_3080_, size_t v_i_3081_, lean_object* v_b_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
uint8_t v___x_3088_; 
v___x_3088_ = lean_usize_dec_lt(v_i_3081_, v_sz_3080_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; 
lean_dec_ref(v_s_3077_);
lean_dec_ref(v_t_3076_);
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_b_3082_);
return v___x_3089_;
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v_a_3092_; lean_object* v___x_3093_; 
lean_dec_ref(v_b_3082_);
v___x_3090_ = lean_box(0);
v___x_3091_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_a_3092_ = lean_array_uget_borrowed(v_as_3079_, v_i_3081_);
lean_inc(v_a_3092_);
lean_inc_ref(v_s_3077_);
lean_inc_ref(v_t_3076_);
v___x_3093_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_3076_, v_s_3077_, v_a_3092_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3108_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3108_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3108_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
uint8_t v___x_3098_; 
v___x_3098_ = lean_unbox(v_a_3094_);
lean_dec(v_a_3094_);
if (v___x_3098_ == 0)
{
size_t v___x_3099_; size_t v___x_3100_; 
lean_del_object(v___x_3096_);
v___x_3099_ = ((size_t)1ULL);
v___x_3100_ = lean_usize_add(v_i_3081_, v___x_3099_);
v_i_3081_ = v___x_3100_;
v_b_3082_ = v___x_3091_;
goto _start;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_dec_ref(v_s_3077_);
lean_dec_ref(v_t_3076_);
v___x_3102_ = lean_box(v___x_3078_);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
lean_ctor_set(v___x_3104_, 1, v___x_3090_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3104_);
v___x_3106_ = v___x_3096_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v_s_3077_);
lean_dec_ref(v_t_3076_);
v_a_3109_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3093_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3093_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object* v_t_3117_, lean_object* v_s_3118_, lean_object* v___x_3119_, lean_object* v_as_3120_, lean_object* v_sz_3121_, lean_object* v_i_3122_, lean_object* v_b_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v___x_2922__boxed_3129_; size_t v_sz_boxed_3130_; size_t v_i_boxed_3131_; lean_object* v_res_3132_; 
v___x_2922__boxed_3129_ = lean_unbox(v___x_3119_);
v_sz_boxed_3130_ = lean_unbox_usize(v_sz_3121_);
lean_dec(v_sz_3121_);
v_i_boxed_3131_ = lean_unbox_usize(v_i_3122_);
lean_dec(v_i_3122_);
v_res_3132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_3117_, v_s_3118_, v___x_2922__boxed_3129_, v_as_3120_, v_sz_boxed_3130_, v_i_boxed_3131_, v_b_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec_ref(v_as_3120_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* v_t_3133_, lean_object* v_s_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v_toCold_3214_; lean_object* v_options_3215_; uint8_t v_hasTrace_3216_; 
v_toCold_3214_ = lean_ctor_get(v_a_3137_, 0);
v_options_3215_ = lean_ctor_get(v_toCold_3214_, 2);
v_hasTrace_3216_ = lean_ctor_get_uint8(v_options_3215_, sizeof(void*)*1);
if (v_hasTrace_3216_ == 0)
{
v___y_3141_ = v_a_3135_;
v___y_3142_ = v_a_3136_;
v___y_3143_ = v_a_3137_;
v___y_3144_ = v_a_3138_;
goto v___jp_3140_;
}
else
{
lean_object* v_inheritedTraceOptions_3217_; lean_object* v_cls_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v_inheritedTraceOptions_3217_ = lean_ctor_get(v_toCold_3214_, 11);
v_cls_3218_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_3219_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7);
v___x_3220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3217_, v_options_3215_, v___x_3219_);
if (v___x_3220_ == 0)
{
v___y_3141_ = v_a_3135_;
v___y_3142_ = v_a_3136_;
v___y_3143_ = v_a_3137_;
v___y_3144_ = v_a_3138_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_inc_ref(v_t_3133_);
v___x_3221_ = l_Lean_MessageData_ofExpr(v_t_3133_);
v___x_3222_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_3223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3221_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
lean_inc_ref(v_s_3134_);
v___x_3224_ = l_Lean_MessageData_ofExpr(v_s_3134_);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_3218_, v___x_3225_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_dec_ref_known(v___x_3226_, 1);
v___y_3141_ = v_a_3135_;
v___y_3142_ = v_a_3136_;
v___y_3143_ = v_a_3137_;
v___y_3144_ = v_a_3138_;
goto v___jp_3140_;
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref(v_s_3134_);
lean_dec_ref(v_t_3133_);
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
v___jp_3140_:
{
lean_object* v___x_3145_; uint8_t v_unificationHints_3146_; 
v___x_3145_ = l_Lean_Meta_Context_config(v___y_3141_);
v_unificationHints_3146_ = lean_ctor_get_uint8(v___x_3145_, 5);
lean_dec_ref(v___x_3145_);
if (v_unificationHints_3146_ == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_dec_ref(v_s_3134_);
lean_dec_ref(v_t_3133_);
v___x_3147_ = lean_box(v_unificationHints_3146_);
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
else
{
uint8_t v___x_3149_; 
v___x_3149_ = l_Lean_Expr_isMVar(v_t_3133_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; 
v___x_3150_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_getRecordedHints(v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3152_; lean_object* v_config_3153_; uint8_t v_trackZetaDelta_3154_; lean_object* v_zetaDeltaSet_3155_; lean_object* v_lctx_3156_; lean_object* v_localInstances_3157_; lean_object* v_defEqCtx_x3f_3158_; lean_object* v_synthPendingDepth_3159_; lean_object* v_customCanUnfoldPredicate_x3f_3160_; uint8_t v_univApprox_3161_; uint8_t v_inTypeClassResolution_3162_; uint8_t v_cacheInferType_3163_; uint64_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v___x_3152_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_3153_ = lean_ctor_get(v___x_3152_, 0);
v_trackZetaDelta_3154_ = lean_ctor_get_uint8(v___y_3141_, sizeof(void*)*7);
v_zetaDeltaSet_3155_ = lean_ctor_get(v___y_3141_, 1);
v_lctx_3156_ = lean_ctor_get(v___y_3141_, 2);
v_localInstances_3157_ = lean_ctor_get(v___y_3141_, 3);
v_defEqCtx_x3f_3158_ = lean_ctor_get(v___y_3141_, 4);
v_synthPendingDepth_3159_ = lean_ctor_get(v___y_3141_, 5);
v_customCanUnfoldPredicate_x3f_3160_ = lean_ctor_get(v___y_3141_, 6);
v_univApprox_3161_ = lean_ctor_get_uint8(v___y_3141_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3162_ = lean_ctor_get_uint8(v___y_3141_, sizeof(void*)*7 + 2);
v_cacheInferType_3163_ = lean_ctor_get_uint8(v___y_3141_, sizeof(void*)*7 + 3);
v___x_3164_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_3153_);
lean_inc_ref(v_config_3153_);
v___x_3165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3165_, 0, v_config_3153_);
lean_ctor_set_uint64(v___x_3165_, sizeof(void*)*1, v___x_3164_);
lean_inc(v_customCanUnfoldPredicate_x3f_3160_);
lean_inc(v_synthPendingDepth_3159_);
lean_inc(v_defEqCtx_x3f_3158_);
lean_inc_ref(v_localInstances_3157_);
lean_inc_ref(v_lctx_3156_);
lean_inc(v_zetaDeltaSet_3155_);
v___x_3166_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v_zetaDeltaSet_3155_);
lean_ctor_set(v___x_3166_, 2, v_lctx_3156_);
lean_ctor_set(v___x_3166_, 3, v_localInstances_3157_);
lean_ctor_set(v___x_3166_, 4, v_defEqCtx_x3f_3158_);
lean_ctor_set(v___x_3166_, 5, v_synthPendingDepth_3159_);
lean_ctor_set(v___x_3166_, 6, v_customCanUnfoldPredicate_x3f_3160_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*7, v_trackZetaDelta_3154_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*7 + 1, v_univApprox_3161_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3162_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*7 + 3, v_cacheInferType_3163_);
lean_inc_ref(v_t_3133_);
v___x_3167_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_a_3151_, v_t_3133_, v___x_3166_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec_ref_known(v___x_3166_, 7);
lean_dec(v_a_3151_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3169_; size_t v_sz_3170_; size_t v___x_3171_; lean_object* v___x_3172_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3167_, 1);
v___x_3169_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_sz_3170_ = lean_array_size(v_a_3168_);
v___x_3171_ = ((size_t)0ULL);
v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_3133_, v_s_3134_, v_unificationHints_3146_, v_a_3168_, v_sz_3170_, v___x_3171_, v___x_3169_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v_a_3168_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3186_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3175_ = v___x_3172_;
v_isShared_3176_ = v_isSharedCheck_3186_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3186_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_fst_3177_; 
v_fst_3177_ = lean_ctor_get(v_a_3173_, 0);
lean_inc(v_fst_3177_);
lean_dec(v_a_3173_);
if (lean_obj_tag(v_fst_3177_) == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3178_ = lean_box(v___x_3149_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3178_);
v___x_3180_ = v___x_3175_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
else
{
lean_object* v_val_3182_; lean_object* v___x_3184_; 
v_val_3182_ = lean_ctor_get(v_fst_3177_, 0);
lean_inc(v_val_3182_);
lean_dec_ref_known(v_fst_3177_, 1);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v_val_3182_);
v___x_3184_ = v___x_3175_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_val_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
v_a_3187_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3172_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3172_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec_ref(v_s_3134_);
lean_dec_ref(v_t_3133_);
v_a_3195_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3167_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3167_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec_ref(v_s_3134_);
lean_dec_ref(v_t_3133_);
v_a_3203_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3150_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3150_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
uint8_t v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
lean_dec_ref(v_s_3134_);
lean_dec_ref(v_t_3133_);
v___x_3211_ = 0;
v___x_3212_ = lean_box(v___x_3211_);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
return v___x_3213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___boxed(lean_object* v_t_3235_, lean_object* v_s_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_Meta_tryUnificationHints(v_t_3235_, v_s_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
return v_res_3242_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = lean_unsigned_to_nat(2674080740u);
v___x_3244_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3245_ = l_Lean_Name_num___override(v___x_3244_, v___x_3243_);
return v___x_3245_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3246_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3247_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3248_ = l_Lean_Name_str___override(v___x_3247_, v___x_3246_);
return v___x_3248_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3250_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3251_ = l_Lean_Name_str___override(v___x_3250_, v___x_3249_);
return v___x_3251_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3252_ = lean_unsigned_to_nat(2u);
v___x_3253_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3254_ = l_Lean_Name_num___override(v___x_3253_, v___x_3252_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3256_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_3257_ = 0;
v___x_3258_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3259_ = l_Lean_registerTraceClass(v___x_3256_, v___x_3257_, v___x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(lean_object* v_a_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
return v_res_3261_;
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
