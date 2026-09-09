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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
lean_object* v_ks_137_; lean_object* v_vs_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_156_; 
v_ks_137_ = lean_ctor_get(v_x_86_, 0);
v_vs_138_ = lean_ctor_get(v_x_86_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_156_ == 0)
{
v___x_140_ = v_x_86_;
v_isShared_141_ = v_isSharedCheck_156_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_vs_138_);
lean_inc(v_ks_137_);
lean_dec(v_x_86_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_156_;
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
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_ks_137_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_vs_138_);
v___x_143_ = v_reuseFailAlloc_155_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v_newNode_144_; size_t v___x_145_; uint8_t v___x_146_; 
v_newNode_144_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10___redArg(v___x_143_, v_x_89_, v_x_90_);
v___x_145_ = ((size_t)7ULL);
v___x_146_ = lean_usize_dec_le(v___x_145_, v_x_88_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_147_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_144_);
v___x_148_ = lean_unsigned_to_nat(4u);
v___x_149_ = lean_nat_dec_lt(v___x_147_, v___x_148_);
lean_dec(v___x_147_);
if (v___x_149_ == 0)
{
lean_object* v_ks_150_; lean_object* v_vs_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_ks_150_ = lean_ctor_get(v_newNode_144_, 0);
lean_inc_ref(v_ks_150_);
v_vs_151_ = lean_ctor_get(v_newNode_144_, 1);
lean_inc_ref(v_vs_151_);
lean_dec_ref(v_newNode_144_);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___closed__0);
v___x_154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg(v_x_88_, v_ks_150_, v_vs_151_, v___x_152_, v___x_153_);
lean_dec_ref(v_vs_151_);
lean_dec_ref(v_ks_150_);
return v___x_154_;
}
else
{
return v_newNode_144_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg(size_t v_depth_157_, lean_object* v_keys_158_, lean_object* v_vals_159_, lean_object* v_i_160_, lean_object* v_entries_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_array_get_size(v_keys_158_);
v___x_163_ = lean_nat_dec_lt(v_i_160_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec(v_i_160_);
return v_entries_161_;
}
else
{
lean_object* v_k_164_; lean_object* v_v_165_; uint64_t v___x_166_; size_t v_h_167_; size_t v___x_168_; lean_object* v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v_h_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_k_164_ = lean_array_fget_borrowed(v_keys_158_, v_i_160_);
v_v_165_ = lean_array_fget_borrowed(v_vals_159_, v_i_160_);
v___x_166_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_164_);
v_h_167_ = lean_uint64_to_usize(v___x_166_);
v___x_168_ = ((size_t)5ULL);
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = ((size_t)1ULL);
v___x_171_ = lean_usize_sub(v_depth_157_, v___x_170_);
v___x_172_ = lean_usize_mul(v___x_168_, v___x_171_);
v_h_173_ = lean_usize_shift_right(v_h_167_, v___x_172_);
v___x_174_ = lean_nat_add(v_i_160_, v___x_169_);
lean_dec(v_i_160_);
lean_inc(v_v_165_);
lean_inc(v_k_164_);
v___x_175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(v_entries_161_, v_h_173_, v_depth_157_, v_k_164_, v_v_165_);
v_i_160_ = v___x_174_;
v_entries_161_ = v___x_175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_depth_177_, lean_object* v_keys_178_, lean_object* v_vals_179_, lean_object* v_i_180_, lean_object* v_entries_181_){
_start:
{
size_t v_depth_boxed_182_; lean_object* v_res_183_; 
v_depth_boxed_182_ = lean_unbox_usize(v_depth_177_);
lean_dec(v_depth_177_);
v_res_183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg(v_depth_boxed_182_, v_keys_178_, v_vals_179_, v_i_180_, v_entries_181_);
lean_dec_ref(v_vals_179_);
lean_dec_ref(v_keys_178_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
size_t v_x_1647__boxed_189_; size_t v_x_1648__boxed_190_; lean_object* v_res_191_; 
v_x_1647__boxed_189_ = lean_unbox_usize(v_x_185_);
lean_dec(v_x_185_);
v_x_1648__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_res_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(v_x_184_, v_x_1647__boxed_189_, v_x_1648__boxed_190_, v_x_187_, v_x_188_);
return v_res_191_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(lean_object* v_a_192_, lean_object* v_b_193_){
_start:
{
lean_object* v_fst_194_; lean_object* v_fst_195_; uint8_t v___x_196_; 
v_fst_194_ = lean_ctor_get(v_a_192_, 0);
v_fst_195_ = lean_ctor_get(v_b_193_, 0);
v___x_196_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_194_, v_fst_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_a_197_, v_b_198_);
lean_dec_ref(v_b_198_);
lean_dec_ref(v_a_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(lean_object* v_x_201_, lean_object* v_keys_202_, lean_object* v_v_203_, lean_object* v_k_204_, lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_c_208_; lean_object* v___x_209_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_add(v_x_201_, v___x_206_);
v_c_208_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_202_, v_v_203_, v___x_207_);
lean_dec(v___x_207_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v_k_204_);
lean_ctor_set(v___x_209_, 1, v_c_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_x_210_, lean_object* v_keys_211_, lean_object* v_v_212_, lean_object* v_k_213_, lean_object* v_x_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(v_x_210_, v_keys_211_, v_v_212_, v_k_213_, v_x_214_);
lean_dec_ref(v_keys_211_);
lean_dec(v_x_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_vs_216_, lean_object* v_v_217_, lean_object* v_i_218_){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_array_get_size(v_vs_216_);
v___x_220_ = lean_nat_dec_lt(v_i_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec(v_i_218_);
v___x_221_ = lean_array_push(v_vs_216_, v_v_217_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_array_fget_borrowed(v_vs_216_, v_i_218_);
v___x_223_ = lean_name_eq(v_v_217_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_add(v_i_218_, v___x_224_);
lean_dec(v_i_218_);
v_i_218_ = v___x_225_;
goto _start;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = lean_array_fset(v_vs_216_, v_i_218_, v_v_217_);
lean_dec(v_i_218_);
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(lean_object* v_vs_228_, lean_object* v_v_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(v_vs_228_, v_v_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_236_, lean_object* v_keys_237_, lean_object* v_v_238_, lean_object* v_k_239_, lean_object* v_as_240_, lean_object* v_k_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_mid_246_; lean_object* v_midVal_247_; uint8_t v___x_248_; 
v___x_244_ = lean_nat_add(v_x_242_, v_x_243_);
v___x_245_ = lean_unsigned_to_nat(1u);
v_mid_246_ = lean_nat_shiftr(v___x_244_, v___x_245_);
lean_dec(v___x_244_);
v_midVal_247_ = lean_array_fget(v_as_240_, v_mid_246_);
v___x_248_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_midVal_247_, v_k_241_);
if (v___x_248_ == 0)
{
uint8_t v___x_249_; 
lean_dec(v_x_243_);
v___x_249_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_k_241_, v_midVal_247_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
lean_dec(v_x_242_);
v___x_250_ = lean_array_get_size(v_as_240_);
v___x_251_ = lean_nat_dec_lt(v_mid_246_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec(v_midVal_247_);
lean_dec(v_mid_246_);
lean_dec(v_k_239_);
lean_dec(v_v_238_);
return v_as_240_;
}
else
{
lean_object* v_snd_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_264_; 
v_snd_252_ = lean_ctor_get(v_midVal_247_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_midVal_247_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v_midVal_247_, 0);
lean_dec(v_unused_265_);
v___x_254_ = v_midVal_247_;
v_isShared_255_ = v_isSharedCheck_264_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snd_252_);
lean_dec(v_midVal_247_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_264_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v_xs_x27_257_; lean_object* v___x_258_; lean_object* v_c_259_; lean_object* v___x_261_; 
v___x_256_ = lean_box(0);
v_xs_x27_257_ = lean_array_fset(v_as_240_, v_mid_246_, v___x_256_);
v___x_258_ = lean_nat_add(v_x_236_, v___x_245_);
v_c_259_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_237_, v_v_238_, v___x_258_, v_snd_252_);
lean_dec(v___x_258_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_c_259_);
lean_ctor_set(v___x_254_, 0, v_k_239_);
v___x_261_ = v___x_254_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_k_239_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_c_259_);
v___x_261_ = v_reuseFailAlloc_263_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; 
v___x_262_ = lean_array_fset(v_xs_x27_257_, v_mid_246_, v___x_261_);
lean_dec(v_mid_246_);
return v___x_262_;
}
}
}
}
else
{
lean_dec(v_midVal_247_);
v_x_243_ = v_mid_246_;
goto _start;
}
}
else
{
uint8_t v___x_267_; 
lean_dec(v_midVal_247_);
v___x_267_ = lean_nat_dec_eq(v_mid_246_, v_x_242_);
if (v___x_267_ == 0)
{
lean_dec(v_x_242_);
v_x_242_ = v_mid_246_;
goto _start;
}
else
{
lean_object* v___x_269_; lean_object* v_c_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_j_273_; lean_object* v_as_274_; lean_object* v___x_275_; 
lean_dec(v_mid_246_);
lean_dec(v_x_243_);
v___x_269_ = lean_nat_add(v_x_236_, v___x_245_);
v_c_270_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_237_, v_v_238_, v___x_269_);
lean_dec(v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v_k_239_);
lean_ctor_set(v___x_271_, 1, v_c_270_);
v___x_272_ = lean_nat_add(v_x_242_, v___x_245_);
lean_dec(v_x_242_);
v_j_273_ = lean_array_get_size(v_as_240_);
v_as_274_ = lean_array_push(v_as_240_, v___x_271_);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_272_, v_as_274_, v_j_273_);
lean_dec(v___x_272_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(lean_object* v_x_276_, lean_object* v_keys_277_, lean_object* v_v_278_, lean_object* v_k_279_, lean_object* v_as_280_, lean_object* v_k_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_282_ = lean_array_get_size(v_as_280_);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_nat_dec_eq(v___x_282_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_array_fget_borrowed(v_as_280_, v___x_283_);
v___x_286_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_k_281_, v___x_285_);
if (v___x_286_ == 0)
{
uint8_t v___x_287_; 
v___x_287_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v___x_285_, v_k_281_);
if (v___x_287_ == 0)
{
uint8_t v___x_288_; 
v___x_288_ = lean_nat_dec_lt(v___x_283_, v___x_282_);
if (v___x_288_ == 0)
{
lean_dec(v_k_279_);
lean_dec(v_v_278_);
return v_as_280_;
}
else
{
lean_object* v___x_289_; lean_object* v_xs_x27_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_inc(v___x_285_);
v___x_289_ = lean_box(0);
v_xs_x27_290_ = lean_array_fset(v_as_280_, v___x_283_, v___x_289_);
v___x_291_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(v_x_276_, v_keys_277_, v_v_278_, v_k_279_, v___x_285_);
v___x_292_ = lean_array_fset(v_xs_x27_290_, v___x_283_, v___x_291_);
return v___x_292_;
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_sub(v___x_282_, v___x_293_);
v___x_295_ = lean_array_fget_borrowed(v_as_280_, v___x_294_);
v___x_296_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v___x_295_, v_k_281_);
if (v___x_296_ == 0)
{
uint8_t v___x_297_; 
v___x_297_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(v_k_281_, v___x_295_);
if (v___x_297_ == 0)
{
uint8_t v___x_298_; 
v___x_298_ = lean_nat_dec_lt(v___x_294_, v___x_282_);
if (v___x_298_ == 0)
{
lean_dec(v___x_294_);
lean_dec(v_k_279_);
lean_dec(v_v_278_);
return v_as_280_;
}
else
{
lean_object* v___x_299_; lean_object* v_xs_x27_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_inc(v___x_295_);
v___x_299_ = lean_box(0);
v_xs_x27_300_ = lean_array_fset(v_as_280_, v___x_294_, v___x_299_);
v___x_301_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(v_x_276_, v_keys_277_, v_v_278_, v_k_279_, v___x_295_);
v___x_302_ = lean_array_fset(v_xs_x27_300_, v___x_294_, v___x_301_);
lean_dec(v___x_294_);
return v___x_302_;
}
}
else
{
lean_object* v___x_303_; 
v___x_303_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg(v_x_276_, v_keys_277_, v_v_278_, v_k_279_, v_as_280_, v_k_281_, v___x_283_, v___x_294_);
return v___x_303_;
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v___x_294_);
v___x_304_ = lean_box(0);
v___x_305_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(v_x_276_, v_keys_277_, v_v_278_, v_k_279_, v___x_304_);
v___x_306_ = lean_array_push(v_as_280_, v___x_305_);
return v___x_306_;
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_as_309_; lean_object* v___x_310_; 
v___x_307_ = lean_box(0);
v___x_308_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(v_x_276_, v_keys_277_, v_v_278_, v_k_279_, v___x_307_);
v_as_309_ = lean_array_push(v_as_280_, v___x_308_);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_283_, v_as_309_, v___x_282_);
return v___x_310_;
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
v___x_312_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(v_x_276_, v_keys_277_, v_v_278_, v_k_279_, v___x_311_);
v___x_313_ = lean_array_push(v_as_280_, v___x_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object* v_keys_314_, lean_object* v_v_315_, lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
lean_object* v_vs_318_; lean_object* v_children_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_336_; 
v_vs_318_ = lean_ctor_get(v_x_317_, 0);
v_children_319_ = lean_ctor_get(v_x_317_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_317_);
if (v_isSharedCheck_336_ == 0)
{
v___x_321_ = v_x_317_;
v_isShared_322_ = v_isSharedCheck_336_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_children_319_);
lean_inc(v_vs_318_);
lean_dec(v_x_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_336_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_array_get_size(v_keys_314_);
v___x_324_ = lean_nat_dec_lt(v_x_316_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(v_vs_318_, v_v_315_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_325_);
v___x_327_ = v___x_321_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_children_319_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
else
{
lean_object* v_k_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_c_332_; lean_object* v___x_334_; 
v_k_329_ = lean_array_fget_borrowed(v_keys_314_, v_x_316_);
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___closed__1));
lean_inc_n(v_k_329_, 2);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_k_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v_c_332_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(v_x_316_, v_keys_314_, v_v_315_, v_k_329_, v_children_319_, v___x_331_);
lean_dec_ref_known(v___x_331_, 2);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v_c_332_);
v___x_334_ = v___x_321_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_vs_318_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_c_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(lean_object* v_x_337_, lean_object* v_keys_338_, lean_object* v_v_339_, lean_object* v_k_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_snd_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_352_; 
v_snd_342_ = lean_ctor_get(v_x_341_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; 
v_unused_353_ = lean_ctor_get(v_x_341_, 0);
lean_dec(v_unused_353_);
v___x_344_ = v_x_341_;
v_isShared_345_ = v_isSharedCheck_352_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_snd_342_);
lean_dec(v_x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_352_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_c_348_; lean_object* v___x_350_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_x_337_, v___x_346_);
v_c_348_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_338_, v_v_339_, v___x_347_, v_snd_342_);
lean_dec(v___x_347_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v_c_348_);
lean_ctor_set(v___x_344_, 0, v_k_340_);
v___x_350_ = v___x_344_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_k_340_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_c_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_354_, lean_object* v_keys_355_, lean_object* v_v_356_, lean_object* v_k_357_, lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(v_x_354_, v_keys_355_, v_v_356_, v_k_357_, v_x_358_);
lean_dec_ref(v_keys_355_);
lean_dec(v_x_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object* v_keys_360_, lean_object* v_v_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_360_, v_v_361_, v_x_362_, v_x_363_);
lean_dec(v_x_362_);
lean_dec_ref(v_keys_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_365_, lean_object* v_keys_366_, lean_object* v_v_367_, lean_object* v_k_368_, lean_object* v_as_369_, lean_object* v_k_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg(v_x_365_, v_keys_366_, v_v_367_, v_k_368_, v_as_369_, v_k_370_, v_x_371_, v_x_372_);
lean_dec_ref(v_k_370_);
lean_dec_ref(v_keys_366_);
lean_dec(v_x_365_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___boxed(lean_object* v_x_374_, lean_object* v_keys_375_, lean_object* v_v_376_, lean_object* v_k_377_, lean_object* v_as_378_, lean_object* v_k_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(v_x_374_, v_keys_375_, v_v_376_, v_k_377_, v_as_378_, v_k_379_);
lean_dec_ref(v_k_379_);
lean_dec_ref(v_keys_375_);
lean_dec(v_x_374_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(lean_object* v_keys_381_, lean_object* v_v_382_, lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_381_, v_v_382_, v___x_384_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_396_; 
v_val_387_ = lean_ctor_get(v_x_383_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_383_);
if (v_isSharedCheck_396_ == 0)
{
v___x_389_ = v_x_383_;
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_val_387_);
lean_dec(v_x_383_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_keys_381_, v_v_382_, v___x_391_, v_val_387_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_397_, lean_object* v_v_398_, lean_object* v_x_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_397_, v_v_398_, v_x_399_);
lean_dec_ref(v_keys_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(lean_object* v_keys_401_, lean_object* v_v_402_, lean_object* v_x_403_, size_t v_x_404_, size_t v_x_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_403_) == 0)
{
lean_object* v_es_407_; size_t v___x_408_; size_t v___x_409_; lean_object* v_j_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v_es_407_ = lean_ctor_get(v_x_403_, 0);
v___x_408_ = ((size_t)31ULL);
v___x_409_ = lean_usize_land(v_x_404_, v___x_408_);
v_j_410_ = lean_usize_to_nat(v___x_409_);
v___x_411_ = lean_array_get_size(v_es_407_);
v___x_412_ = lean_nat_dec_lt(v_j_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_dec(v_j_410_);
lean_dec(v_x_406_);
lean_dec(v_v_402_);
return v_x_403_;
}
else
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_480_; 
lean_inc_ref(v_es_407_);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_403_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v_x_403_, 0);
lean_dec(v_unused_481_);
v___x_414_ = v_x_403_;
v_isShared_415_ = v_isSharedCheck_480_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_x_403_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_480_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_v_416_; lean_object* v___x_417_; lean_object* v_xs_x27_418_; lean_object* v___y_420_; 
v_v_416_ = lean_array_fget(v_es_407_, v_j_410_);
v___x_417_ = lean_box(0);
v_xs_x27_418_ = lean_array_fset(v_es_407_, v_j_410_, v___x_417_);
switch(lean_obj_tag(v_v_416_))
{
case 0:
{
lean_object* v_key_425_; lean_object* v_val_426_; uint8_t v___x_427_; 
v_key_425_ = lean_ctor_get(v_v_416_, 0);
v_val_426_ = lean_ctor_get(v_v_416_, 1);
v___x_427_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_406_, v_key_425_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_box(0);
v___x_429_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_401_, v_v_402_, v___x_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_dec(v_x_406_);
v___y_420_ = v_v_416_;
goto v___jp_419_;
}
else
{
lean_object* v_val_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_438_; 
lean_inc(v_val_426_);
lean_inc(v_key_425_);
lean_dec_ref_known(v_v_416_, 2);
v_val_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_438_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_val_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_425_, v_val_426_, v_x_406_, v_val_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
v___y_420_ = v___x_436_;
goto v___jp_419_;
}
}
}
}
else
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_449_; 
lean_inc(v_val_426_);
v_isSharedCheck_449_ = !lean_is_exclusive(v_v_416_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; lean_object* v_unused_451_; 
v_unused_450_ = lean_ctor_get(v_v_416_, 1);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_v_416_, 0);
lean_dec(v_unused_451_);
v___x_440_ = v_v_416_;
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_v_416_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_val_426_);
v___x_443_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_401_, v_v_402_, v___x_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v___x_444_; 
lean_del_object(v___x_440_);
lean_dec(v_x_406_);
v___x_444_ = lean_box(2);
v___y_420_ = v___x_444_;
goto v___jp_419_;
}
else
{
lean_object* v_val_445_; lean_object* v___x_447_; 
v_val_445_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v___x_443_, 1);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v_val_445_);
lean_ctor_set(v___x_440_, 0, v_x_406_);
v___x_447_ = v___x_440_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_x_406_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_val_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
v___y_420_ = v___x_447_;
goto v___jp_419_;
}
}
}
}
}
case 1:
{
lean_object* v_node_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_475_; 
v_node_452_ = lean_ctor_get(v_v_416_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_v_416_);
if (v_isSharedCheck_475_ == 0)
{
v___x_454_ = v_v_416_;
v_isShared_455_ = v_isSharedCheck_475_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_node_452_);
lean_dec(v_v_416_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_475_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v_newNode_460_; lean_object* v___x_461_; 
v___x_456_ = ((size_t)5ULL);
v___x_457_ = lean_usize_shift_right(v_x_404_, v___x_456_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_x_405_, v___x_458_);
v_newNode_460_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(v_keys_401_, v_v_402_, v_node_452_, v___x_457_, v___x_459_, v_x_406_);
lean_inc_ref(v_newNode_460_);
v___x_461_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_460_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_463_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_newNode_460_);
v___x_463_ = v___x_454_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_newNode_460_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
v___y_420_ = v___x_463_;
goto v___jp_419_;
}
}
else
{
lean_object* v_val_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v_newNode_460_);
lean_del_object(v___x_454_);
v_val_465_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v___x_461_, 1);
v_fst_466_ = lean_ctor_get(v_val_465_, 0);
v_snd_467_ = lean_ctor_get(v_val_465_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_val_465_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v_val_465_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_inc(v_fst_466_);
lean_dec(v_val_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_fst_466_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_snd_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
v___y_420_ = v___x_472_;
goto v___jp_419_;
}
}
}
}
}
default: 
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_box(0);
v___x_477_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_401_, v_v_402_, v___x_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_dec(v_x_406_);
v___y_420_ = v_v_416_;
goto v___jp_419_;
}
else
{
lean_object* v_val_478_; lean_object* v___x_479_; 
v_val_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v___x_477_, 1);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_x_406_);
lean_ctor_set(v___x_479_, 1, v_val_478_);
v___y_420_ = v___x_479_;
goto v___jp_419_;
}
}
}
v___jp_419_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_array_fset(v_xs_x27_418_, v_j_410_, v___y_420_);
lean_dec(v_j_410_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_421_);
v___x_423_ = v___x_414_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
else
{
lean_object* v_ks_482_; lean_object* v_vs_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_516_; 
v_ks_482_ = lean_ctor_get(v_x_403_, 0);
v_vs_483_ = lean_ctor_get(v_x_403_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_403_);
if (v_isSharedCheck_516_ == 0)
{
v___x_485_ = v_x_403_;
v_isShared_486_ = v_isSharedCheck_516_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_vs_483_);
lean_inc(v_ks_482_);
lean_dec(v_x_403_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_516_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; 
v___x_487_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__4(v_ks_482_, v_x_406_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_489_; 
if (v_isShared_486_ == 0)
{
v___x_489_ = v___x_485_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_ks_482_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_vs_483_);
v___x_489_ = v_reuseFailAlloc_494_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_box(0);
v___x_491_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_401_, v_v_402_, v___x_490_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_dec(v_x_406_);
return v___x_489_;
}
else
{
lean_object* v_val_492_; lean_object* v___x_493_; 
v_val_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_val_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(v___x_489_, v_x_404_, v_x_405_, v_x_406_, v_val_492_);
return v___x_493_;
}
}
}
else
{
lean_object* v_val_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_515_; 
v_val_495_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_515_ == 0)
{
v___x_497_ = v___x_487_;
v_isShared_498_ = v_isSharedCheck_515_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_val_495_);
lean_dec(v___x_487_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_515_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_v_x27_499_; lean_object* v_keys_500_; lean_object* v_vals_501_; lean_object* v___x_503_; 
v_v_x27_499_ = lean_array_fget(v_vs_483_, v_val_495_);
lean_inc(v_val_495_);
v_keys_500_ = l_Array_eraseIdx___redArg(v_ks_482_, v_val_495_);
v_vals_501_ = l_Array_eraseIdx___redArg(v_vs_483_, v_val_495_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v_v_x27_499_);
v___x_503_ = v___x_497_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_v_x27_499_);
v___x_503_ = v_reuseFailAlloc_514_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___lam__0(v_keys_401_, v_v_402_, v___x_503_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v___x_506_; 
lean_dec(v_x_406_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v_vals_501_);
lean_ctor_set(v___x_485_, 0, v_keys_500_);
v___x_506_ = v___x_485_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_keys_500_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_vals_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
else
{
lean_object* v_val_508_; lean_object* v_keys_509_; lean_object* v_vals_510_; lean_object* v___x_512_; 
v_val_508_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v___x_504_, 1);
v_keys_509_ = lean_array_push(v_keys_500_, v_x_406_);
v_vals_510_ = lean_array_push(v_vals_501_, v_val_508_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v_vals_510_);
lean_ctor_set(v___x_485_, 0, v_keys_509_);
v___x_512_ = v___x_485_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_keys_509_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_vals_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___boxed(lean_object* v_keys_517_, lean_object* v_v_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
size_t v_x_2068__boxed_523_; size_t v_x_2069__boxed_524_; lean_object* v_res_525_; 
v_x_2068__boxed_523_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_x_2069__boxed_524_ = lean_unbox_usize(v_x_521_);
lean_dec(v_x_521_);
v_res_525_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(v_keys_517_, v_v_518_, v_x_519_, v_x_2068__boxed_523_, v_x_2069__boxed_524_, v_x_522_);
lean_dec_ref(v_keys_517_);
return v_res_525_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(lean_object* v_msg_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0);
v___x_529_ = lean_panic_fn_borrowed(v___x_528_, v_msg_527_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_533_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2));
v___x_534_ = lean_unsigned_to_nat(23u);
v___x_535_ = lean_unsigned_to_nat(166u);
v___x_536_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1));
v___x_537_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0));
v___x_538_ = l_mkPanicMessageWithDecl(v___x_537_, v___x_536_, v___x_535_, v___x_534_, v___x_533_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(lean_object* v_d_539_, lean_object* v_keys_540_, lean_object* v_v_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_array_get_size(v_keys_540_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_nat_dec_eq(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v_k_546_; uint64_t v___x_547_; size_t v_h_548_; size_t v___x_549_; lean_object* v___x_550_; 
v___x_545_ = lean_box(0);
v_k_546_ = lean_array_get_borrowed(v___x_545_, v_keys_540_, v___x_543_);
v___x_547_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_546_);
v_h_548_ = lean_uint64_to_usize(v___x_547_);
v___x_549_ = ((size_t)1ULL);
lean_inc(v_k_546_);
v___x_550_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(v_keys_540_, v_v_541_, v_d_539_, v_h_548_, v___x_549_, v_k_546_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec(v_v_541_);
lean_dec_ref(v_d_539_);
v___x_551_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3);
v___x_552_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v___x_551_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___boxed(lean_object* v_d_553_, lean_object* v_keys_554_, lean_object* v_v_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_d_553_, v_keys_554_, v_v_555_);
lean_dec_ref(v_keys_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* v_hints_557_, lean_object* v_e_558_){
_start:
{
lean_object* v_keys_559_; lean_object* v_val_560_; lean_object* v___x_561_; 
v_keys_559_ = lean_ctor_get(v_e_558_, 0);
lean_inc_ref(v_keys_559_);
v_val_560_ = lean_ctor_get(v_e_558_, 1);
lean_inc(v_val_560_);
lean_dec_ref(v_e_558_);
v___x_561_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(v_hints_557_, v_keys_559_, v_val_560_);
lean_dec_ref(v_keys_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_562_, lean_object* v_x_563_, size_t v_x_564_, size_t v_x_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___redArg(v_x_563_, v_x_564_, v_x_565_, v_x_566_, v_x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
size_t v_x_2336__boxed_575_; size_t v_x_2337__boxed_576_; lean_object* v_res_577_; 
v_x_2336__boxed_575_ = lean_unbox_usize(v_x_571_);
lean_dec(v_x_571_);
v_x_2337__boxed_576_ = lean_unbox_usize(v_x_572_);
lean_dec(v_x_572_);
v_res_577_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5(v_00_u03b2_569_, v_x_570_, v_x_2336__boxed_575_, v_x_2337__boxed_576_, v_x_573_, v_x_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_578_, lean_object* v_keys_579_, lean_object* v_v_580_, lean_object* v_k_581_, lean_object* v_as_582_, lean_object* v_k_583_, lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___redArg(v_x_578_, v_keys_579_, v_v_580_, v_k_581_, v_as_582_, v_k_583_, v_x_584_, v_x_585_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_589_, lean_object* v_keys_590_, lean_object* v_v_591_, lean_object* v_k_592_, lean_object* v_as_593_, lean_object* v_k_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__5(v_x_589_, v_keys_590_, v_v_591_, v_k_592_, v_as_593_, v_k_594_, v_x_595_, v_x_596_, v_x_597_, v_x_598_);
lean_dec_ref(v_k_594_);
lean_dec_ref(v_keys_590_);
lean_dec(v_x_589_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_600_, lean_object* v_n_601_, lean_object* v_k_602_, lean_object* v_v_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10___redArg(v_n_601_, v_k_602_, v_v_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_605_, size_t v_depth_606_, lean_object* v_keys_607_, lean_object* v_vals_608_, lean_object* v_heq_609_, lean_object* v_i_610_, lean_object* v_entries_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___redArg(v_depth_606_, v_keys_607_, v_vals_608_, v_i_610_, v_entries_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_613_, lean_object* v_depth_614_, lean_object* v_keys_615_, lean_object* v_vals_616_, lean_object* v_heq_617_, lean_object* v_i_618_, lean_object* v_entries_619_){
_start:
{
size_t v_depth_boxed_620_; lean_object* v_res_621_; 
v_depth_boxed_620_ = lean_unbox_usize(v_depth_614_);
lean_dec(v_depth_614_);
v_res_621_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__11(v_00_u03b2_613_, v_depth_boxed_620_, v_keys_615_, v_vals_616_, v_heq_617_, v_i_618_, v_entries_619_);
lean_dec_ref(v_vals_616_);
lean_dec_ref(v_keys_615_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10_spec__11(lean_object* v_00_u03b2_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__5_spec__10_spec__11___redArg(v_x_623_, v_x_624_, v_x_625_, v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object* v_x_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v_a_629_);
lean_inc_ref_n(v___x_630_, 2);
v___x_631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
lean_ctor_set(v___x_631_, 2, v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_x_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v_x_632_, v_a_633_);
lean_dec_ref(v_x_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(lean_object* v___y_635_){
_start:
{
lean_inc_ref(v___y_635_);
return v___y_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v___y_636_);
lean_dec_ref(v___y_636_);
return v_res_637_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___f_648_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___f_649_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_650_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_));
v___x_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v___x_650_);
lean_ctor_set(v___x_653_, 3, v___f_649_);
lean_ctor_set(v___x_653_, 4, v___f_648_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_);
v___x_656_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
return v_res_658_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object* v_e_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1));
v___x_667_ = lean_unsigned_to_nat(3u);
v___x_668_ = l_Lean_Expr_isAppOfArity(v_e_665_, v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3);
v___x_670_ = l_Lean_indentExpr(v_e_665_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_673_ = l_Lean_Expr_appFn_x21(v_e_665_);
v___x_674_ = l_Lean_Expr_appArg_x21(v___x_673_);
lean_dec_ref(v___x_673_);
v___x_675_ = l_Lean_Expr_appArg_x21(v_e_665_);
lean_dec_ref(v_e_665_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0));
v___x_680_ = l_Lean_stringToMessageData(v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object* v_e_681_, lean_object* v_cs_682_){
_start:
{
if (lean_obj_tag(v_e_681_) == 7)
{
lean_object* v_binderType_683_; lean_object* v_body_684_; lean_object* v___x_685_; 
v_binderType_683_ = lean_ctor_get(v_e_681_, 1);
v_body_684_ = lean_ctor_get(v_e_681_, 2);
lean_inc_ref(v_binderType_683_);
v___x_685_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_binderType_683_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref_known(v_e_681_, 3);
lean_dec_ref(v_cs_682_);
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_707_; 
v_a_694_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_707_ == 0)
{
v___x_696_ = v___x_685_;
v_isShared_697_ = v_isSharedCheck_707_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_685_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_707_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_Expr_hasLooseBVars(v_body_684_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
lean_inc_ref(v_body_684_);
lean_del_object(v___x_696_);
lean_dec_ref_known(v_e_681_, 3);
v___x_699_ = lean_array_push(v_cs_682_, v_a_694_);
v_e_681_ = v_body_684_;
v_cs_682_ = v___x_699_;
goto _start;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
lean_dec(v_a_694_);
lean_dec_ref(v_cs_682_);
v___x_701_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1);
v___x_702_ = l_Lean_indentExpr(v_e_681_);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 0);
lean_ctor_set(v___x_696_, 0, v___x_703_);
v___x_705_ = v___x_696_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_object* v___x_708_; 
v___x_708_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_e_681_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v_cs_682_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_726_; 
v_a_717_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_726_ == 0)
{
v___x_719_ = v___x_708_;
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_708_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_721_ = lean_array_to_list(v_cs_682_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_a_717_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object* v_e_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0));
v___x_731_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(v_e_729_, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(lean_object* v_msgData_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; lean_object* v_env_739_; lean_object* v___x_740_; lean_object* v_toCold_741_; lean_object* v_mctx_742_; lean_object* v_lctx_743_; lean_object* v_options_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_738_ = lean_st_ref_get(v___y_736_);
v_env_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_env_739_);
lean_dec(v___x_738_);
v___x_740_ = lean_st_ref_get(v___y_734_);
v_toCold_741_ = lean_ctor_get(v___y_735_, 0);
v_mctx_742_ = lean_ctor_get(v___x_740_, 0);
lean_inc_ref(v_mctx_742_);
lean_dec(v___x_740_);
v_lctx_743_ = lean_ctor_get(v___y_733_, 2);
v_options_744_ = lean_ctor_get(v_toCold_741_, 2);
lean_inc_ref(v_options_744_);
lean_inc_ref(v_lctx_743_);
v___x_745_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_745_, 0, v_env_739_);
lean_ctor_set(v___x_745_, 1, v_mctx_742_);
lean_ctor_set(v___x_745_, 2, v_lctx_743_);
lean_ctor_set(v___x_745_, 3, v_options_744_);
v___x_746_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_msgData_732_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object* v_msgData_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msgData_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_ref_761_; lean_object* v___x_762_; lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_ref_761_ = lean_ctor_get(v___y_758_, 2);
v___x_762_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_771_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_inc(v_ref_761_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_ref_761_);
lean_ctor_set(v___x_767_, 1, v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 1);
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg___boxed(lean_object* v_msg_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_778_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(lean_object* v_as_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
if (lean_obj_tag(v_as_785_) == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
else
{
lean_object* v_head_793_; lean_object* v_tail_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_828_; 
v_head_793_ = lean_ctor_get(v_as_785_, 0);
v_tail_794_ = lean_ctor_get(v_as_785_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_as_785_);
if (v_isSharedCheck_828_ == 0)
{
v___x_796_ = v_as_785_;
v_isShared_797_ = v_isSharedCheck_828_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_tail_794_);
lean_inc(v_head_793_);
lean_dec(v_as_785_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_828_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_lhs_798_; lean_object* v_rhs_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_827_; 
v_lhs_798_ = lean_ctor_get(v_head_793_, 0);
v_rhs_799_ = lean_ctor_get(v_head_793_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_head_793_);
if (v_isSharedCheck_827_ == 0)
{
v___x_801_ = v_head_793_;
v_isShared_802_ = v_isSharedCheck_827_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_rhs_799_);
lean_inc(v_lhs_798_);
lean_dec(v_head_793_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_827_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; 
lean_inc_ref(v_rhs_799_);
lean_inc_ref(v_lhs_798_);
v___x_803_ = l_Lean_Meta_isExprDefEq(v_lhs_798_, v_rhs_799_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; uint8_t v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v___x_805_ = lean_unbox(v_a_804_);
lean_dec(v_a_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
lean_dec(v_tail_794_);
v___x_806_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1);
v___x_807_ = l_Lean_indentExpr(v_lhs_798_);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 7);
lean_ctor_set(v___x_801_, 1, v___x_807_);
lean_ctor_set(v___x_801_, 0, v___x_806_);
v___x_809_ = v___x_801_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_817_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 7);
lean_ctor_set(v___x_796_, 1, v___x_810_);
lean_ctor_set(v___x_796_, 0, v___x_809_);
v___x_812_ = v___x_796_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = l_Lean_indentExpr(v_rhs_799_);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_814_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
return v___x_815_;
}
}
}
else
{
lean_del_object(v___x_801_);
lean_dec_ref(v_rhs_799_);
lean_dec_ref(v_lhs_798_);
lean_del_object(v___x_796_);
v_as_785_ = v_tail_794_;
goto _start;
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_del_object(v___x_801_);
lean_dec_ref(v_rhs_799_);
lean_dec_ref(v_lhs_798_);
lean_del_object(v___x_796_);
lean_dec(v_tail_794_);
v_a_819_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_803_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_803_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___boxed(lean_object* v_as_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_as_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_835_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0));
v___x_838_ = l_Lean_stringToMessageData(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object* v_hint_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_pattern_845_; lean_object* v_constraints_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_888_; 
v_pattern_845_ = lean_ctor_get(v_hint_839_, 0);
v_constraints_846_ = lean_ctor_get(v_hint_839_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_hint_839_);
if (v_isSharedCheck_888_ == 0)
{
v___x_848_ = v_hint_839_;
v_isShared_849_ = v_isSharedCheck_888_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_constraints_846_);
lean_inc(v_pattern_845_);
lean_dec(v_hint_839_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_888_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; 
v___x_850_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_constraints_846_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_lhs_851_; lean_object* v_rhs_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref_known(v___x_850_, 1);
v_lhs_851_ = lean_ctor_get(v_pattern_845_, 0);
v_rhs_852_ = lean_ctor_get(v_pattern_845_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_pattern_845_);
if (v_isSharedCheck_887_ == 0)
{
v___x_854_ = v_pattern_845_;
v_isShared_855_ = v_isSharedCheck_887_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_rhs_852_);
lean_inc(v_lhs_851_);
lean_dec(v_pattern_845_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_887_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; 
lean_inc_ref(v_rhs_852_);
lean_inc_ref(v_lhs_851_);
v___x_856_ = l_Lean_Meta_isExprDefEq(v_lhs_851_, v_rhs_852_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_878_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_878_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_878_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_878_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
uint8_t v___x_861_; 
v___x_861_ = lean_unbox(v_a_857_);
lean_dec(v_a_857_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
lean_del_object(v___x_859_);
v___x_862_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1);
v___x_863_ = l_Lean_indentExpr(v_lhs_851_);
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 7);
lean_ctor_set(v___x_854_, 1, v___x_863_);
lean_ctor_set(v___x_854_, 0, v___x_862_);
v___x_865_ = v___x_854_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_873_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_866_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 7);
lean_ctor_set(v___x_848_, 1, v___x_866_);
lean_ctor_set(v___x_848_, 0, v___x_865_);
v___x_868_ = v___x_848_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_866_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = l_Lean_indentExpr(v_rhs_852_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_870_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
return v___x_871_;
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_del_object(v___x_854_);
lean_dec_ref(v_rhs_852_);
lean_dec_ref(v_lhs_851_);
lean_del_object(v___x_848_);
v___x_874_ = lean_box(0);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_874_);
v___x_876_ = v___x_859_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_del_object(v___x_854_);
lean_dec_ref(v_rhs_852_);
lean_dec_ref(v_lhs_851_);
lean_del_object(v___x_848_);
v_a_879_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_856_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_856_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
else
{
lean_del_object(v___x_848_);
lean_dec_ref(v_pattern_845_);
return v___x_850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object* v_hint_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_hint_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object* v_00_u03b1_896_, lean_object* v_msg_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object* v_00_u03b1_904_, lean_object* v_msg_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(v_00_u03b1_904_, v_msg_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_911_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_912_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_918_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
lean_ctor_set(v___x_918_, 2, v___x_917_);
lean_ctor_set(v___x_918_, 3, v___x_917_);
lean_ctor_set(v___x_918_, 4, v___x_917_);
lean_ctor_set(v___x_918_, 5, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(lean_object* v_ext_919_, lean_object* v_b_920_, uint8_t v_kind_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_toCold_926_; lean_object* v_currNamespace_927_; lean_object* v___x_928_; lean_object* v_env_929_; lean_object* v_nextMacroScope_930_; lean_object* v_ngen_931_; lean_object* v_auxDeclNGen_932_; lean_object* v_traceState_933_; lean_object* v_messages_934_; lean_object* v_infoState_935_; lean_object* v_snapshotTasks_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_963_; 
v_toCold_926_ = lean_ctor_get(v___y_923_, 0);
v_currNamespace_927_ = lean_ctor_get(v_toCold_926_, 4);
v___x_928_ = lean_st_ref_take(v___y_924_);
v_env_929_ = lean_ctor_get(v___x_928_, 0);
v_nextMacroScope_930_ = lean_ctor_get(v___x_928_, 1);
v_ngen_931_ = lean_ctor_get(v___x_928_, 2);
v_auxDeclNGen_932_ = lean_ctor_get(v___x_928_, 3);
v_traceState_933_ = lean_ctor_get(v___x_928_, 4);
v_messages_934_ = lean_ctor_get(v___x_928_, 6);
v_infoState_935_ = lean_ctor_get(v___x_928_, 7);
v_snapshotTasks_936_ = lean_ctor_get(v___x_928_, 8);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v___x_928_, 5);
lean_dec(v_unused_964_);
v___x_938_ = v___x_928_;
v_isShared_939_ = v_isSharedCheck_963_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snapshotTasks_936_);
lean_inc(v_infoState_935_);
lean_inc(v_messages_934_);
lean_inc(v_traceState_933_);
lean_inc(v_auxDeclNGen_932_);
lean_inc(v_ngen_931_);
lean_inc(v_nextMacroScope_930_);
lean_inc(v_env_929_);
lean_dec(v___x_928_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_963_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
lean_inc(v_currNamespace_927_);
v___x_940_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_929_, v_ext_919_, v_b_920_, v_kind_921_, v_currNamespace_927_);
v___x_941_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 5, v___x_941_);
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_nextMacroScope_930_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_ngen_931_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_auxDeclNGen_932_);
lean_ctor_set(v_reuseFailAlloc_962_, 4, v_traceState_933_);
lean_ctor_set(v_reuseFailAlloc_962_, 5, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_962_, 6, v_messages_934_);
lean_ctor_set(v_reuseFailAlloc_962_, 7, v_infoState_935_);
lean_ctor_set(v_reuseFailAlloc_962_, 8, v_snapshotTasks_936_);
v___x_943_ = v_reuseFailAlloc_962_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_mctx_946_; lean_object* v_zetaDeltaFVarIds_947_; lean_object* v_postponed_948_; lean_object* v_diag_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_960_; 
v___x_944_ = lean_st_ref_put(v___y_924_, v___x_943_);
v___x_945_ = lean_st_ref_take(v___y_922_);
v_mctx_946_ = lean_ctor_get(v___x_945_, 0);
v_zetaDeltaFVarIds_947_ = lean_ctor_get(v___x_945_, 2);
v_postponed_948_ = lean_ctor_get(v___x_945_, 3);
v_diag_949_ = lean_ctor_get(v___x_945_, 4);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v___x_945_, 1);
lean_dec(v_unused_961_);
v___x_951_ = v___x_945_;
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_diag_949_);
lean_inc(v_postponed_948_);
lean_inc(v_zetaDeltaFVarIds_947_);
lean_inc(v_mctx_946_);
lean_dec(v___x_945_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v___x_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_mctx_946_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_zetaDeltaFVarIds_947_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_postponed_948_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_diag_949_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = lean_st_ref_put(v___y_922_, v___x_955_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(lean_object* v_ext_965_, lean_object* v_b_966_, lean_object* v_kind_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
uint8_t v_kind_boxed_972_; lean_object* v_res_973_; 
v_kind_boxed_972_ = lean_unbox(v_kind_967_);
v_res_973_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_965_, v_b_966_, v_kind_boxed_972_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object* v_00_u03b1_974_, lean_object* v_00_u03b2_975_, lean_object* v_00_u03c3_976_, lean_object* v_ext_977_, lean_object* v_b_978_, uint8_t v_kind_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_977_, v_b_978_, v_kind_979_, v___y_981_, v___y_982_, v___y_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object* v_00_u03b1_986_, lean_object* v_00_u03b2_987_, lean_object* v_00_u03c3_988_, lean_object* v_ext_989_, lean_object* v_b_990_, lean_object* v_kind_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v_kind_boxed_997_; lean_object* v_res_998_; 
v_kind_boxed_997_ = lean_unbox(v_kind_991_);
v_res_998_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(v_00_u03b1_986_, v_00_u03b2_987_, v_00_u03c3_988_, v_ext_989_, v_b_990_, v_kind_boxed_997_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(lean_object* v_k_999_, uint8_t v_allowLevelAssignments_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1000_, v_k_999_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1006_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1006_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(lean_object* v_k_1023_, lean_object* v_allowLevelAssignments_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1030_; lean_object* v_res_1031_; 
v_allowLevelAssignments_boxed_1030_ = lean_unbox(v_allowLevelAssignments_1024_);
v_res_1031_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_1023_, v_allowLevelAssignments_boxed_1030_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(lean_object* v_00_u03b1_1032_, lean_object* v_k_1033_, uint8_t v_allowLevelAssignments_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_1033_, v_allowLevelAssignments_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_k_1042_, lean_object* v_allowLevelAssignments_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1049_; lean_object* v_res_1050_; 
v_allowLevelAssignments_boxed_1049_ = lean_unbox(v_allowLevelAssignments_1043_);
v_res_1050_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(v_00_u03b1_1041_, v_k_1042_, v_allowLevelAssignments_boxed_1049_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1050_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
lean_ctor_set(v___x_1056_, 2, v___x_1055_);
lean_ctor_set(v___x_1056_, 3, v___x_1055_);
lean_ctor_set(v___x_1056_, 4, v___x_1054_);
lean_ctor_set(v___x_1056_, 5, v___x_1054_);
lean_ctor_set(v___x_1056_, 6, v___x_1054_);
lean_ctor_set(v___x_1056_, 7, v___x_1054_);
lean_ctor_set(v___x_1056_, 8, v___x_1054_);
lean_ctor_set(v___x_1056_, 9, v___x_1054_);
lean_ctor_set(v___x_1056_, 10, v___x_1054_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_unsigned_to_nat(32u);
v___x_1058_ = lean_mk_empty_array_with_capacity(v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1060_ = ((size_t)5ULL);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_unsigned_to_nat(32u);
v___x_1063_ = lean_mk_empty_array_with_capacity(v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1065_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
lean_ctor_set(v___x_1065_, 2, v___x_1061_);
lean_ctor_set(v___x_1065_, 3, v___x_1061_);
lean_ctor_set_usize(v___x_1065_, 4, v___x_1060_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1066_ = lean_box(1);
v___x_1067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
lean_ctor_set(v___x_1069_, 2, v___x_1066_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1091_, lean_object* v_declHint_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v_env_1096_; uint8_t v___x_1097_; 
v___x_1095_ = lean_st_ref_get(v___y_1093_);
v_env_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_env_1096_);
lean_dec(v___x_1095_);
v___x_1097_ = l_Lean_Name_isAnonymous(v_declHint_1092_);
if (v___x_1097_ == 0)
{
uint8_t v_isExporting_1098_; 
v_isExporting_1098_ = lean_ctor_get_uint8(v_env_1096_, sizeof(void*)*8);
if (v_isExporting_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref(v_env_1096_);
lean_dec(v_declHint_1092_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_msg_1091_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
lean_inc_ref(v_env_1096_);
v___x_1100_ = l_Lean_Environment_setExporting(v_env_1096_, v___x_1097_);
lean_inc(v_declHint_1092_);
lean_inc_ref(v___x_1100_);
v___x_1101_ = l_Lean_Environment_contains(v___x_1100_, v_declHint_1092_, v_isExporting_1098_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_env_1096_);
lean_dec(v_declHint_1092_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_msg_1091_);
return v___x_1102_;
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_c_1108_; lean_object* v___x_1109_; 
v___x_1103_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1104_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1105_ = l_Lean_Options_empty;
v___x_1106_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1100_);
lean_ctor_set(v___x_1106_, 1, v___x_1103_);
lean_ctor_set(v___x_1106_, 2, v___x_1104_);
lean_ctor_set(v___x_1106_, 3, v___x_1105_);
lean_inc(v_declHint_1092_);
v___x_1107_ = l_Lean_MessageData_ofConstName(v_declHint_1092_, v___x_1097_);
v_c_1108_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1108_, 0, v___x_1106_);
lean_ctor_set(v_c_1108_, 1, v___x_1107_);
v___x_1109_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1096_, v_declHint_1092_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec_ref(v_env_1096_);
lean_dec(v_declHint_1092_);
v___x_1110_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v_c_1108_);
v___x_1112_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = l_Lean_MessageData_note(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_msg_1091_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
else
{
lean_object* v_val_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1152_; 
v_val_1117_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1119_ = v___x_1109_;
v_isShared_1120_ = v_isSharedCheck_1152_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_val_1117_);
lean_dec(v___x_1109_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1152_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_mod_1124_; uint8_t v___x_1125_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = l_Lean_Environment_header(v_env_1096_);
lean_dec_ref(v_env_1096_);
v___x_1123_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1122_);
v_mod_1124_ = lean_array_get(v___x_1121_, v___x_1123_, v_val_1117_);
lean_dec(v_val_1117_);
lean_dec_ref(v___x_1123_);
v___x_1125_ = l_Lean_isPrivateName(v_declHint_1092_);
lean_dec(v_declHint_1092_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v_c_1108_);
v___x_1128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_MessageData_ofName(v_mod_1124_);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = l_Lean_MessageData_note(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_msg_1091_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1135_);
v___x_1137_ = v___x_1119_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v_c_1108_);
v___x_1141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_MessageData_ofName(v_mod_1124_);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = l_Lean_MessageData_note(v___x_1146_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_msg_1091_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1148_);
v___x_1150_ = v___x_1119_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1153_; 
lean_dec_ref(v_env_1096_);
lean_dec(v_declHint_1092_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_msg_1091_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1154_, lean_object* v_declHint_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1154_, v_declHint_1155_, v___y_1156_);
lean_dec(v___y_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object* v_msg_1159_, lean_object* v_declHint_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1176_; 
v___x_1166_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1159_, v_declHint_1160_, v___y_1164_);
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1171_ = l_Lean_unknownIdentifierMessageTag;
v___x_1172_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1177_, lean_object* v_declHint_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1177_, v_declHint_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1185_, lean_object* v_msg_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_toCold_1192_; lean_object* v_currRecDepth_1193_; lean_object* v_ref_1194_; uint8_t v_diag_1195_; uint8_t v_suppressElabErrors_1196_; lean_object* v_ref_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_toCold_1192_ = lean_ctor_get(v___y_1189_, 0);
v_currRecDepth_1193_ = lean_ctor_get(v___y_1189_, 1);
v_ref_1194_ = lean_ctor_get(v___y_1189_, 2);
v_diag_1195_ = lean_ctor_get_uint8(v___y_1189_, sizeof(void*)*3);
v_suppressElabErrors_1196_ = lean_ctor_get_uint8(v___y_1189_, sizeof(void*)*3 + 1);
v_ref_1197_ = l_Lean_replaceRef(v_ref_1185_, v_ref_1194_);
lean_inc(v_currRecDepth_1193_);
lean_inc_ref(v_toCold_1192_);
v___x_1198_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1198_, 0, v_toCold_1192_);
lean_ctor_set(v___x_1198_, 1, v_currRecDepth_1193_);
lean_ctor_set(v___x_1198_, 2, v_ref_1197_);
lean_ctor_set_uint8(v___x_1198_, sizeof(void*)*3, v_diag_1195_);
lean_ctor_set_uint8(v___x_1198_, sizeof(void*)*3 + 1, v_suppressElabErrors_1196_);
v___x_1199_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_1186_, v___y_1187_, v___y_1188_, v___x_1198_, v___y_1190_);
lean_dec_ref_known(v___x_1198_, 3);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1200_, lean_object* v_msg_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1200_, v_msg_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v_ref_1200_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_ref_1208_, lean_object* v_msg_1209_, lean_object* v_declHint_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v_a_1217_; lean_object* v___x_1218_; 
v___x_1216_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1209_, v_declHint_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref(v___x_1216_);
v___x_1218_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1208_, v_a_1217_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1219_, lean_object* v_msg_1220_, lean_object* v_declHint_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1219_, v_msg_1220_, v_declHint_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v_ref_1219_);
return v_res_1227_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1234_, lean_object* v_constName_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1241_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1242_ = 0;
lean_inc(v_constName_1235_);
v___x_1243_ = l_Lean_MessageData_ofConstName(v_constName_1235_, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1241_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1234_, v___x_1246_, v_constName_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1248_, lean_object* v_constName_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1248_, v_constName_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v_ref_1248_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(lean_object* v_constName_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_ref_1262_; lean_object* v___x_1263_; 
v_ref_1262_ = lean_ctor_get(v___y_1259_, 2);
v___x_1263_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1262_, v_constName_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(lean_object* v_constName_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; lean_object* v_env_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; 
v___x_1277_ = lean_st_ref_get(v___y_1275_);
v_env_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc_ref(v_env_1278_);
lean_dec(v___x_1277_);
v___x_1279_ = 0;
lean_inc(v_constName_1271_);
v___x_1280_ = l_Lean_Environment_find_x3f(v_env_1278_, v_constName_1271_, v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1281_;
}
else
{
lean_object* v_val_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_constName_1271_);
v_val_1282_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1280_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_val_1282_);
lean_dec(v___x_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 0);
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_val_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(lean_object* v_constName_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_constName_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
return v_res_1296_;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_Meta_addUnificationHint___lam__0___closed__0));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object* v_declName_1300_, uint8_t v_kind_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
lean_inc(v_declName_1300_);
v___x_1307_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_declName_1300_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1309_ = 0;
v___x_1310_ = l_Lean_ConstantInfo_value_x3f(v_a_1308_, v___x_1309_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec(v_declName_1300_);
v___x_1311_ = lean_obj_once(&l_Lean_Meta_addUnificationHint___lam__0___closed__1, &l_Lean_Meta_addUnificationHint___lam__0___closed__1_once, _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1);
v___x_1312_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_1311_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1312_;
}
else
{
lean_object* v_val_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_val_1313_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1314_ = lean_box(0);
v___x_1315_ = l_Lean_Meta_lambdaMetaTelescope(v_val_1313_, v___x_1314_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v_val_1313_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v_snd_1317_; lean_object* v_snd_1318_; lean_object* v___x_1319_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v_snd_1317_ = lean_ctor_get(v_a_1316_, 1);
lean_inc(v_snd_1317_);
lean_dec(v_a_1316_);
v_snd_1318_ = lean_ctor_get(v_snd_1317_, 1);
lean_inc(v_snd_1318_);
lean_dec(v_snd_1317_);
v___x_1319_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_1318_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; 
lean_dec(v_declName_1300_);
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_a_1320_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1321_;
}
else
{
lean_object* v_a_1322_; lean_object* v_pattern_1323_; lean_object* v_lhs_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1359_; 
v_a_1322_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1319_, 1);
v_pattern_1323_ = lean_ctor_get(v_a_1322_, 0);
lean_inc_ref(v_pattern_1323_);
v_lhs_1324_ = lean_ctor_get(v_pattern_1323_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_pattern_1323_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v_pattern_1323_, 1);
lean_dec(v_unused_1360_);
v___x_1326_ = v_pattern_1323_;
v_isShared_1327_ = v_isSharedCheck_1359_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_lhs_1324_);
lean_dec(v_pattern_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1359_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v_config_1329_; uint8_t v_trackZetaDelta_1330_; lean_object* v_zetaDeltaSet_1331_; lean_object* v_lctx_1332_; lean_object* v_localInstances_1333_; lean_object* v_defEqCtx_x3f_1334_; lean_object* v_synthPendingDepth_1335_; lean_object* v_customCanUnfoldPredicate_x3f_1336_; uint8_t v_univApprox_1337_; uint8_t v_inTypeClassResolution_1338_; uint8_t v_cacheInferType_1339_; uint64_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1328_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_1329_ = lean_ctor_get(v___x_1328_, 0);
v_trackZetaDelta_1330_ = lean_ctor_get_uint8(v___y_1302_, sizeof(void*)*7);
v_zetaDeltaSet_1331_ = lean_ctor_get(v___y_1302_, 1);
v_lctx_1332_ = lean_ctor_get(v___y_1302_, 2);
v_localInstances_1333_ = lean_ctor_get(v___y_1302_, 3);
v_defEqCtx_x3f_1334_ = lean_ctor_get(v___y_1302_, 4);
v_synthPendingDepth_1335_ = lean_ctor_get(v___y_1302_, 5);
v_customCanUnfoldPredicate_x3f_1336_ = lean_ctor_get(v___y_1302_, 6);
v_univApprox_1337_ = lean_ctor_get_uint8(v___y_1302_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1338_ = lean_ctor_get_uint8(v___y_1302_, sizeof(void*)*7 + 2);
v_cacheInferType_1339_ = lean_ctor_get_uint8(v___y_1302_, sizeof(void*)*7 + 3);
v___x_1340_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1329_);
lean_inc_ref(v_config_1329_);
v___x_1341_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1341_, 0, v_config_1329_);
lean_ctor_set_uint64(v___x_1341_, sizeof(void*)*1, v___x_1340_);
lean_inc(v_customCanUnfoldPredicate_x3f_1336_);
lean_inc(v_synthPendingDepth_1335_);
lean_inc(v_defEqCtx_x3f_1334_);
lean_inc_ref(v_localInstances_1333_);
lean_inc_ref(v_lctx_1332_);
lean_inc(v_zetaDeltaSet_1331_);
v___x_1342_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_zetaDeltaSet_1331_);
lean_ctor_set(v___x_1342_, 2, v_lctx_1332_);
lean_ctor_set(v___x_1342_, 3, v_localInstances_1333_);
lean_ctor_set(v___x_1342_, 4, v_defEqCtx_x3f_1334_);
lean_ctor_set(v___x_1342_, 5, v_synthPendingDepth_1335_);
lean_ctor_set(v___x_1342_, 6, v_customCanUnfoldPredicate_x3f_1336_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*7, v_trackZetaDelta_1330_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*7 + 1, v_univApprox_1337_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1338_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*7 + 3, v_cacheInferType_1339_);
v___x_1343_ = l_Lean_Meta_DiscrTree_mkPath(v_lhs_1324_, v___x_1309_, v___x_1342_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec_ref_known(v___x_1342_, 7);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_a_1322_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_dec_ref_known(v___x_1345_, 1);
v___x_1346_ = l_Lean_Meta_unificationHintExtension;
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_declName_1300_);
lean_ctor_set(v___x_1326_, 0, v_a_1344_);
v___x_1348_ = v___x_1326_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_declName_1300_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v___x_1346_, v___x_1348_, v_kind_1301_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1349_;
}
}
else
{
lean_dec(v_a_1344_);
lean_del_object(v___x_1326_);
lean_dec(v_declName_1300_);
return v___x_1345_;
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_del_object(v___x_1326_);
lean_dec(v_a_1322_);
lean_dec(v_declName_1300_);
v_a_1351_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1343_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1343_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_declName_1300_);
v_a_1361_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1315_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1315_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v_declName_1300_);
v_a_1369_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1307_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1307_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object* v_declName_1377_, lean_object* v_kind_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_kind_boxed_1384_; lean_object* v_res_1385_; 
v_kind_boxed_1384_ = lean_unbox(v_kind_1378_);
v_res_1385_ = l_Lean_Meta_addUnificationHint___lam__0(v_declName_1377_, v_kind_boxed_1384_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* v_declName_1386_, uint8_t v_kind_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v___x_1393_; lean_object* v___f_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; 
v___x_1393_ = lean_box(v_kind_1387_);
v___f_1394_ = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1394_, 0, v_declName_1386_);
lean_closure_set(v___f_1394_, 1, v___x_1393_);
v___x_1395_ = 0;
v___x_1396_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v___f_1394_, v___x_1395_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* v_declName_1397_, lean_object* v_kind_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
uint8_t v_kind_boxed_1404_; lean_object* v_res_1405_; 
v_kind_boxed_1404_ = lean_unbox(v_kind_1398_);
v_res_1405_ = l_Lean_Meta_addUnificationHint(v_declName_1397_, v_kind_boxed_1404_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object* v_00_u03b1_1406_, lean_object* v_constName_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1414_, lean_object* v_constName_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(v_00_u03b1_1414_, v_constName_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1422_, lean_object* v_ref_1423_, lean_object* v_constName_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1423_, v_constName_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1431_, lean_object* v_ref_1432_, lean_object* v_constName_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(v_00_u03b1_1431_, v_ref_1432_, v_constName_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v_ref_1432_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_1440_, lean_object* v_ref_1441_, lean_object* v_msg_1442_, lean_object* v_declHint_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1441_, v_msg_1442_, v_declHint_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1450_, lean_object* v_ref_1451_, lean_object* v_msg_1452_, lean_object* v_declHint_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(v_00_u03b1_1450_, v_ref_1451_, v_msg_1452_, v_declHint_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v_ref_1451_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1460_, lean_object* v_declHint_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1460_, v_declHint_1461_, v___y_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1468_, lean_object* v_declHint_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(v_msg_1468_, v_declHint_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1476_, lean_object* v_ref_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1477_, v_msg_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1485_, lean_object* v_ref_1486_, lean_object* v_msg_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(v_00_u03b1_1485_, v_ref_1486_, v_msg_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v_ref_1486_);
return v_res_1493_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1500_; uint64_t v___x_1501_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1501_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1503_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1504_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set_uint64(v___x_1504_, sizeof(void*)*1, v___x_1502_);
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1509_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
lean_ctor_set(v___x_1509_, 2, v___x_1508_);
lean_ctor_set(v___x_1509_, 3, v___x_1508_);
lean_ctor_set(v___x_1509_, 4, v___x_1508_);
lean_ctor_set(v___x_1509_, 5, v___x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
lean_ctor_set(v___x_1511_, 2, v___x_1510_);
lean_ctor_set(v___x_1511_, 3, v___x_1510_);
lean_ctor_set(v___x_1511_, 4, v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1512_, lean_object* v___x_1513_, lean_object* v_declName_1514_, lean_object* v_stx_1515_, uint8_t v_kind_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1515_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1520_) == 0)
{
uint8_t v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec_ref_known(v___x_1520_, 1);
v___x_1521_ = 0;
v___x_1522_ = 1;
v___x_1523_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1524_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1525_ = lean_unsigned_to_nat(32u);
v___x_1526_ = lean_mk_empty_array_with_capacity(v___x_1525_);
v___x_1527_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1528_ = ((size_t)5ULL);
lean_inc_n(v___x_1512_, 6);
v___x_1529_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1526_);
lean_ctor_set(v___x_1529_, 2, v___x_1512_);
lean_ctor_set(v___x_1529_, 3, v___x_1512_);
lean_ctor_set_usize(v___x_1529_, 4, v___x_1528_);
v___x_1530_ = lean_box(1);
lean_inc_ref(v___x_1529_);
v___x_1531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1524_);
lean_ctor_set(v___x_1531_, 1, v___x_1529_);
lean_ctor_set(v___x_1531_, 2, v___x_1530_);
v___x_1532_ = lean_mk_empty_array_with_capacity(v___x_1512_);
v___x_1533_ = lean_box(0);
lean_inc(v___x_1513_);
v___x_1534_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1534_, 0, v___x_1523_);
lean_ctor_set(v___x_1534_, 1, v___x_1513_);
lean_ctor_set(v___x_1534_, 2, v___x_1531_);
lean_ctor_set(v___x_1534_, 3, v___x_1532_);
lean_ctor_set(v___x_1534_, 4, v___x_1533_);
lean_ctor_set(v___x_1534_, 5, v___x_1512_);
lean_ctor_set(v___x_1534_, 6, v___x_1533_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*7, v___x_1521_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*7 + 1, v___x_1521_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*7 + 2, v___x_1521_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*7 + 3, v___x_1522_);
v___x_1535_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1512_);
lean_ctor_set(v___x_1535_, 1, v___x_1512_);
lean_ctor_set(v___x_1535_, 2, v___x_1512_);
lean_ctor_set(v___x_1535_, 3, v___x_1512_);
lean_ctor_set(v___x_1535_, 4, v___x_1524_);
lean_ctor_set(v___x_1535_, 5, v___x_1524_);
lean_ctor_set(v___x_1535_, 6, v___x_1524_);
lean_ctor_set(v___x_1535_, 7, v___x_1524_);
lean_ctor_set(v___x_1535_, 8, v___x_1524_);
lean_ctor_set(v___x_1535_, 9, v___x_1524_);
lean_ctor_set(v___x_1535_, 10, v___x_1524_);
v___x_1536_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1537_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1535_);
lean_ctor_set(v___x_1538_, 1, v___x_1536_);
lean_ctor_set(v___x_1538_, 2, v___x_1513_);
lean_ctor_set(v___x_1538_, 3, v___x_1529_);
lean_ctor_set(v___x_1538_, 4, v___x_1537_);
v___x_1539_ = lean_st_mk_ref(v___x_1538_);
v___x_1540_ = l_Lean_Meta_addUnificationHint(v_declName_1514_, v_kind_1516_, v___x_1534_, v___x_1539_, v___y_1517_, v___y_1518_);
lean_dec_ref_known(v___x_1534_, 7);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1549_; 
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v___x_1540_, 0);
lean_dec(v_unused_1550_);
v___x_1542_ = v___x_1540_;
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
else
{
lean_dec(v___x_1540_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1544_ = lean_st_ref_get(v___x_1539_);
lean_dec(v___x_1539_);
lean_dec(v___x_1544_);
v___x_1545_ = lean_box(0);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1545_);
v___x_1547_ = v___x_1542_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
lean_dec(v___x_1539_);
return v___x_1540_;
}
}
else
{
lean_dec(v_declName_1514_);
lean_dec(v___x_1513_);
lean_dec(v___x_1512_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1551_, lean_object* v___x_1552_, lean_object* v_declName_1553_, lean_object* v_stx_1554_, lean_object* v_kind_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
uint8_t v_kind_boxed_1559_; lean_object* v_res_1560_; 
v_kind_boxed_1559_ = lean_unbox(v_kind_1555_);
v_res_1560_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1551_, v___x_1552_, v_declName_1553_, v_stx_1554_, v_kind_boxed_1559_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v_toCold_1566_; lean_object* v_env_1567_; lean_object* v_options_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1565_ = lean_st_ref_get(v___y_1563_);
v_toCold_1566_ = lean_ctor_get(v___y_1562_, 0);
v_env_1567_ = lean_ctor_get(v___x_1565_, 0);
lean_inc_ref(v_env_1567_);
lean_dec(v___x_1565_);
v_options_1568_ = lean_ctor_get(v_toCold_1566_, 2);
v___x_1569_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1570_ = lean_unsigned_to_nat(32u);
v___x_1571_ = lean_mk_empty_array_with_capacity(v___x_1570_);
lean_dec_ref(v___x_1571_);
v___x_1572_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_1568_);
v___x_1573_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1573_, 0, v_env_1567_);
lean_ctor_set(v___x_1573_, 1, v___x_1569_);
lean_ctor_set(v___x_1573_, 2, v___x_1572_);
lean_ctor_set(v___x_1573_, 3, v_options_1568_);
v___x_1574_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_msgData_1561_);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_ref_1585_; lean_object* v___x_1586_; lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1595_; 
v_ref_1585_ = lean_ctor_get(v___y_1582_, 2);
v___x_1586_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msg_1581_, v___y_1582_, v___y_1583_);
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_inc(v_ref_1585_);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v_ref_1585_);
lean_ctor_set(v___x_1591_, 1, v_a_1587_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 1);
lean_ctor_set(v___x_1589_, 0, v___x_1591_);
v___x_1593_ = v___x_1589_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1600_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1603_ = l_Lean_stringToMessageData(v___x_1602_);
return v___x_1603_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1606_ = l_Lean_stringToMessageData(v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1607_, lean_object* v_decl_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1612_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1613_ = l_Lean_MessageData_ofName(v___x_1607_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v___x_1616_, v___y_1609_, v___y_1610_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1618_, lean_object* v_decl_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1618_, v_decl_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v_decl_1619_);
return v_res_1623_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = lean_unsigned_to_nat(3033092106u);
v___x_1668_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1669_ = l_Lean_Name_num___override(v___x_1668_, v___x_1667_);
return v___x_1669_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1672_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1673_ = l_Lean_Name_str___override(v___x_1672_, v___x_1671_);
return v___x_1673_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1676_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1677_ = l_Lean_Name_str___override(v___x_1676_, v___x_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = lean_unsigned_to_nat(2u);
v___x_1679_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1680_ = l_Lean_Name_num___override(v___x_1679_, v___x_1678_);
return v___x_1680_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1687_ = 0;
v___x_1688_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1689_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1690_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1691_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v___x_1689_);
lean_ctor_set(v___x_1691_, 2, v___x_1688_);
lean_ctor_set_uint8(v___x_1691_, sizeof(void*)*3, v___x_1687_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___f_1692_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___f_1693_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___f_1693_);
lean_ctor_set(v___x_1695_, 2, v___f_1692_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1698_ = l_Lean_registerBuiltinAttribute(v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1701_, lean_object* v_msg_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1702_, v___y_1703_, v___y_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1707_, lean_object* v_msg_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(v_00_u03b1_1707_, v_msg_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* v_p_1713_, lean_object* v_e_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___y_1721_; lean_object* v___x_1738_; uint8_t v_transparency_1739_; uint8_t v___x_1740_; uint8_t v___x_1741_; 
v___x_1738_ = l_Lean_Meta_Context_config(v_a_1715_);
v_transparency_1739_ = lean_ctor_get_uint8(v___x_1738_, 9);
lean_dec_ref(v___x_1738_);
v___x_1740_ = 2;
v___x_1741_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1739_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v_keyedConfig_1742_; uint8_t v_trackZetaDelta_1743_; lean_object* v_zetaDeltaSet_1744_; lean_object* v_lctx_1745_; lean_object* v_localInstances_1746_; lean_object* v_defEqCtx_x3f_1747_; lean_object* v_synthPendingDepth_1748_; lean_object* v_customCanUnfoldPredicate_x3f_1749_; uint8_t v_univApprox_1750_; uint8_t v_inTypeClassResolution_1751_; uint8_t v_cacheInferType_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_keyedConfig_1742_ = lean_ctor_get(v_a_1715_, 0);
v_trackZetaDelta_1743_ = lean_ctor_get_uint8(v_a_1715_, sizeof(void*)*7);
v_zetaDeltaSet_1744_ = lean_ctor_get(v_a_1715_, 1);
v_lctx_1745_ = lean_ctor_get(v_a_1715_, 2);
v_localInstances_1746_ = lean_ctor_get(v_a_1715_, 3);
v_defEqCtx_x3f_1747_ = lean_ctor_get(v_a_1715_, 4);
v_synthPendingDepth_1748_ = lean_ctor_get(v_a_1715_, 5);
v_customCanUnfoldPredicate_x3f_1749_ = lean_ctor_get(v_a_1715_, 6);
v_univApprox_1750_ = lean_ctor_get_uint8(v_a_1715_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1751_ = lean_ctor_get_uint8(v_a_1715_, sizeof(void*)*7 + 2);
v_cacheInferType_1752_ = lean_ctor_get_uint8(v_a_1715_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1742_);
v___x_1753_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1740_, v_keyedConfig_1742_);
lean_inc(v_customCanUnfoldPredicate_x3f_1749_);
lean_inc(v_synthPendingDepth_1748_);
lean_inc(v_defEqCtx_x3f_1747_);
lean_inc_ref(v_localInstances_1746_);
lean_inc_ref(v_lctx_1745_);
lean_inc(v_zetaDeltaSet_1744_);
v___x_1754_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v_zetaDeltaSet_1744_);
lean_ctor_set(v___x_1754_, 2, v_lctx_1745_);
lean_ctor_set(v___x_1754_, 3, v_localInstances_1746_);
lean_ctor_set(v___x_1754_, 4, v_defEqCtx_x3f_1747_);
lean_ctor_set(v___x_1754_, 5, v_synthPendingDepth_1748_);
lean_ctor_set(v___x_1754_, 6, v_customCanUnfoldPredicate_x3f_1749_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*7, v_trackZetaDelta_1743_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*7 + 1, v_univApprox_1750_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1751_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*7 + 3, v_cacheInferType_1752_);
lean_inc(v_a_1718_);
lean_inc_ref(v_a_1717_);
lean_inc(v_a_1716_);
v___x_1755_ = lean_is_expr_def_eq(v_p_1713_, v_e_1714_, v___x_1754_, v_a_1716_, v_a_1717_, v_a_1718_);
v___y_1721_ = v___x_1755_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_1756_; 
lean_inc(v_a_1718_);
lean_inc_ref(v_a_1717_);
lean_inc(v_a_1716_);
lean_inc_ref(v_a_1715_);
v___x_1756_ = lean_is_expr_def_eq(v_p_1713_, v_e_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_);
v___y_1721_ = v___x_1756_;
goto v___jp_1720_;
}
v___jp_1720_:
{
if (lean_obj_tag(v___y_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1722_ = lean_ctor_get(v___y_1721_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___y_1721_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___y_1721_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___y_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
v_a_1730_ = lean_ctor_get(v___y_1721_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___y_1721_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___y_1721_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___y_1721_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object* v_p_1757_, lean_object* v_e_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_p_1757_, v_e_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
lean_dec(v_a_1762_);
lean_dec_ref(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object* v_x_1765_, lean_object* v_x_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
if (lean_obj_tag(v_x_1765_) == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = l_List_reverse___redArg(v_x_1766_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
else
{
lean_object* v_tail_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1792_; 
v_tail_1774_ = lean_ctor_get(v_x_1765_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_x_1765_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_x_1765_, 0);
lean_dec(v_unused_1793_);
v___x_1776_ = v_x_1765_;
v_isShared_1777_ = v_isSharedCheck_1792_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_tail_1774_);
lean_dec(v_x_1765_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1792_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 1, v_x_1766_);
lean_ctor_set(v___x_1776_, 0, v_a_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1779_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_x_1766_);
v___x_1781_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
v_x_1765_ = v_tail_1774_;
v_x_1766_ = v___x_1781_;
goto _start;
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_del_object(v___x_1776_);
lean_dec(v_tail_1774_);
lean_dec(v_x_1766_);
v_a_1784_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1778_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1778_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object* v_x_1794_, lean_object* v_x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v_x_1794_, v_x_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1801_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1802_; double v___x_1803_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_float_of_nat(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object* v_cls_1807_, lean_object* v_msg_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_ref_1814_; lean_object* v___x_1815_; lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1860_; 
v_ref_1814_ = lean_ctor_get(v___y_1811_, 2);
v___x_1815_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1860_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1860_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v_traceState_1821_; lean_object* v_env_1822_; lean_object* v_nextMacroScope_1823_; lean_object* v_ngen_1824_; lean_object* v_auxDeclNGen_1825_; lean_object* v_cache_1826_; lean_object* v_messages_1827_; lean_object* v_infoState_1828_; lean_object* v_snapshotTasks_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1859_; 
v___x_1820_ = lean_st_ref_take(v___y_1812_);
v_traceState_1821_ = lean_ctor_get(v___x_1820_, 4);
v_env_1822_ = lean_ctor_get(v___x_1820_, 0);
v_nextMacroScope_1823_ = lean_ctor_get(v___x_1820_, 1);
v_ngen_1824_ = lean_ctor_get(v___x_1820_, 2);
v_auxDeclNGen_1825_ = lean_ctor_get(v___x_1820_, 3);
v_cache_1826_ = lean_ctor_get(v___x_1820_, 5);
v_messages_1827_ = lean_ctor_get(v___x_1820_, 6);
v_infoState_1828_ = lean_ctor_get(v___x_1820_, 7);
v_snapshotTasks_1829_ = lean_ctor_get(v___x_1820_, 8);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1831_ = v___x_1820_;
v_isShared_1832_ = v_isSharedCheck_1859_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_snapshotTasks_1829_);
lean_inc(v_infoState_1828_);
lean_inc(v_messages_1827_);
lean_inc(v_cache_1826_);
lean_inc(v_traceState_1821_);
lean_inc(v_auxDeclNGen_1825_);
lean_inc(v_ngen_1824_);
lean_inc(v_nextMacroScope_1823_);
lean_inc(v_env_1822_);
lean_dec(v___x_1820_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1859_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
uint64_t v_tid_1833_; lean_object* v_traces_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1858_; 
v_tid_1833_ = lean_ctor_get_uint64(v_traceState_1821_, sizeof(void*)*1);
v_traces_1834_ = lean_ctor_get(v_traceState_1821_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_traceState_1821_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1836_ = v_traceState_1821_;
v_isShared_1837_ = v_isSharedCheck_1858_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_traces_1834_);
lean_dec(v_traceState_1821_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1858_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; double v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
v___x_1840_ = 0;
v___x_1841_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_1842_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1842_, 0, v_cls_1807_);
lean_ctor_set(v___x_1842_, 1, v___x_1838_);
lean_ctor_set(v___x_1842_, 2, v___x_1841_);
lean_ctor_set_float(v___x_1842_, sizeof(void*)*3, v___x_1839_);
lean_ctor_set_float(v___x_1842_, sizeof(void*)*3 + 8, v___x_1839_);
lean_ctor_set_uint8(v___x_1842_, sizeof(void*)*3 + 16, v___x_1840_);
v___x_1843_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2));
v___x_1844_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v_a_1816_);
lean_ctor_set(v___x_1844_, 2, v___x_1843_);
lean_inc(v_ref_1814_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_ref_1814_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = l_Lean_PersistentArray_push___redArg(v_traces_1834_, v___x_1845_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1846_);
v___x_1848_ = v___x_1836_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1846_);
lean_ctor_set_uint64(v_reuseFailAlloc_1857_, sizeof(void*)*1, v_tid_1833_);
v___x_1848_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 4, v___x_1848_);
v___x_1850_ = v___x_1831_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_env_1822_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_nextMacroScope_1823_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_ngen_1824_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_auxDeclNGen_1825_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1856_, 5, v_cache_1826_);
lean_ctor_set(v_reuseFailAlloc_1856_, 6, v_messages_1827_);
lean_ctor_set(v_reuseFailAlloc_1856_, 7, v_infoState_1828_);
lean_ctor_set(v_reuseFailAlloc_1856_, 8, v_snapshotTasks_1829_);
v___x_1850_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1851_ = lean_st_ref_put(v___y_1812_, v___x_1850_);
v___x_1852_ = lean_box(0);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1852_);
v___x_1854_ = v___x_1818_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object* v_cls_1861_, lean_object* v_msg_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_1861_, v_msg_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object* v_as_1872_, size_t v_sz_1873_, size_t v_i_1874_, lean_object* v_b_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_a_1882_; uint8_t v___x_1886_; 
v___x_1886_ = lean_usize_dec_lt(v_i_1874_, v_sz_1873_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_b_1875_);
return v___x_1887_;
}
else
{
lean_object* v_snd_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1978_; 
v_snd_1888_ = lean_ctor_get(v_b_1875_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_b_1875_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v_b_1875_, 0);
lean_dec(v_unused_1979_);
v___x_1890_ = v_b_1875_;
v_isShared_1891_ = v_isSharedCheck_1978_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_snd_1888_);
lean_dec(v_b_1875_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1978_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_array_1892_; lean_object* v_start_1893_; lean_object* v_stop_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v_array_1892_ = lean_ctor_get(v_snd_1888_, 0);
v_start_1893_ = lean_ctor_get(v_snd_1888_, 1);
v_stop_1894_ = lean_ctor_get(v_snd_1888_, 2);
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_nat_dec_lt(v_start_1893_, v_stop_1894_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1898_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1895_);
v___x_1898_ = v___x_1890_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_snd_1888_);
v___x_1898_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
}
else
{
lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1974_; 
lean_inc(v_stop_1894_);
lean_inc(v_start_1893_);
lean_inc_ref(v_array_1892_);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_snd_1888_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; lean_object* v_unused_1976_; lean_object* v_unused_1977_; 
v_unused_1975_ = lean_ctor_get(v_snd_1888_, 2);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_snd_1888_, 1);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_snd_1888_, 0);
lean_dec(v_unused_1977_);
v___x_1902_ = v_snd_1888_;
v_isShared_1903_ = v_isSharedCheck_1974_;
goto v_resetjp_1901_;
}
else
{
lean_dec(v_snd_1888_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1974_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1904_ = lean_array_fget(v_array_1892_, v_start_1893_);
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_add(v_start_1893_, v___x_1905_);
lean_dec(v_start_1893_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v___x_1906_);
v___x_1908_ = v___x_1902_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_array_1892_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_stop_1894_);
v___x_1908_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
uint8_t v___x_1909_; uint8_t v___x_1910_; uint8_t v___x_1911_; 
v___x_1909_ = 3;
v___x_1910_ = lean_unbox(v___x_1904_);
lean_dec(v___x_1904_);
v___x_1911_ = l_Lean_instBEqBinderInfo_beq(v___x_1910_, v___x_1909_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1913_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v___x_1908_);
lean_ctor_set(v___x_1890_, 0, v___x_1895_);
v___x_1913_ = v___x_1890_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
v_a_1882_ = v___x_1913_;
goto v___jp_1881_;
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1916_; 
v_a_1915_ = lean_array_uget_borrowed(v_as_1872_, v_i_1874_);
lean_inc(v___y_1879_);
lean_inc_ref(v___y_1878_);
lean_inc(v___y_1877_);
lean_inc_ref(v___y_1876_);
lean_inc(v_a_1915_);
v___x_1916_ = lean_infer_type(v_a_1915_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = l_Lean_Meta_trySynthInstance(v_a_1917_, v___x_1895_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1956_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1956_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1956_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
if (lean_obj_tag(v_a_1919_) == 1)
{
lean_object* v_a_1923_; lean_object* v___x_1924_; 
lean_del_object(v___x_1921_);
v_a_1923_ = lean_ctor_get(v_a_1919_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v_a_1919_, 1);
lean_inc(v_a_1915_);
v___x_1924_ = l_Lean_Meta_isExprDefEq(v_a_1915_, v_a_1923_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1940_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1940_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1940_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
uint8_t v___x_1929_; 
v___x_1929_ = lean_unbox(v_a_1925_);
lean_dec(v_a_1925_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v___x_1908_);
lean_ctor_set(v___x_1890_, 0, v___x_1930_);
v___x_1932_ = v___x_1890_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1908_);
v___x_1932_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1934_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1932_);
v___x_1934_ = v___x_1927_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_object* v___x_1938_; 
lean_del_object(v___x_1927_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v___x_1908_);
lean_ctor_set(v___x_1890_, 0, v___x_1895_);
v___x_1938_ = v___x_1890_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1908_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
v_a_1882_ = v___x_1938_;
goto v___jp_1881_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v___x_1908_);
lean_del_object(v___x_1890_);
v_a_1941_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1924_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1924_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
lean_dec(v_a_1919_);
v___x_1949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v___x_1908_);
lean_ctor_set(v___x_1890_, 0, v___x_1949_);
v___x_1951_ = v___x_1890_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1908_);
v___x_1951_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1953_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1951_);
v___x_1953_ = v___x_1921_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v___x_1908_);
lean_del_object(v___x_1890_);
v_a_1957_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1918_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1918_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v___x_1908_);
lean_del_object(v___x_1890_);
v_a_1965_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1916_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1916_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
}
}
}
v___jp_1881_:
{
size_t v___x_1883_; size_t v___x_1884_; 
v___x_1883_ = ((size_t)1ULL);
v___x_1884_ = lean_usize_add(v_i_1874_, v___x_1883_);
v_i_1874_ = v___x_1884_;
v_b_1875_ = v_a_1882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object* v_as_1980_, lean_object* v_sz_1981_, lean_object* v_i_1982_, lean_object* v_b_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
size_t v_sz_boxed_1989_; size_t v_i_boxed_1990_; lean_object* v_res_1991_; 
v_sz_boxed_1989_ = lean_unbox_usize(v_sz_1981_);
lean_dec(v_sz_1981_);
v_i_boxed_1990_ = lean_unbox_usize(v_i_1982_);
lean_dec(v_i_1982_);
v_res_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_as_1980_, v_sz_boxed_1989_, v_i_boxed_1990_, v_b_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_as_1980_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object* v_as_x27_1995_, lean_object* v_b_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
if (lean_obj_tag(v_as_x27_1995_) == 0)
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_b_1996_);
return v___x_2002_;
}
else
{
lean_object* v_head_2003_; lean_object* v_tail_2004_; lean_object* v_lhs_2005_; lean_object* v_rhs_2006_; lean_object* v___x_2007_; 
lean_dec_ref(v_b_1996_);
v_head_2003_ = lean_ctor_get(v_as_x27_1995_, 0);
v_tail_2004_ = lean_ctor_get(v_as_x27_1995_, 1);
v_lhs_2005_ = lean_ctor_get(v_head_2003_, 0);
v_rhs_2006_ = lean_ctor_get(v_head_2003_, 1);
lean_inc(v___y_2000_);
lean_inc_ref(v___y_1999_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1997_);
lean_inc_ref(v_rhs_2006_);
lean_inc_ref(v_lhs_2005_);
v___x_2007_ = lean_is_expr_def_eq(v_lhs_2005_, v_rhs_2006_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2021_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2021_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2021_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = lean_unbox(v_a_2008_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_a_2008_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v___x_2012_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2015_);
v___x_2017_ = v___x_2010_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
else
{
lean_object* v___x_2019_; 
lean_del_object(v___x_2010_);
lean_dec(v_a_2008_);
v___x_2019_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_as_x27_1995_ = v_tail_2004_;
v_b_1996_ = v___x_2019_;
goto _start;
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_a_2022_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2007_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2007_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object* v_as_x27_2030_, lean_object* v_b_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2030_, v_b_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v_as_x27_2030_);
return v_res_2037_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2038_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8(void){
_start:
{
lean_object* v_cls_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_cls_2053_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2054_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7));
v___x_2055_ = l_Lean_Name_append(v___x_2054_, v_cls_2053_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9));
v___x_2058_ = l_Lean_stringToMessageData(v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object* v_candidate_2059_, lean_object* v_t_2060_, lean_object* v_s_2061_, uint8_t v_mayPostpone_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_Meta_saveState___redArg(v_a_2064_, v_a_2066_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2321_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2321_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2321_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___y_2074_; uint8_t v___y_2075_; lean_object* v_a_2097_; uint8_t v_a_2101_; lean_object* v___x_2113_; lean_object* v_cache_2114_; lean_object* v_mctx_2115_; lean_object* v_zetaDeltaFVarIds_2116_; lean_object* v_postponed_2117_; lean_object* v_diag_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2320_; 
v___x_2113_ = lean_st_ref_take(v_a_2064_);
v_cache_2114_ = lean_ctor_get(v___x_2113_, 1);
v_mctx_2115_ = lean_ctor_get(v___x_2113_, 0);
v_zetaDeltaFVarIds_2116_ = lean_ctor_get(v___x_2113_, 2);
v_postponed_2117_ = lean_ctor_get(v___x_2113_, 3);
v_diag_2118_ = lean_ctor_get(v___x_2113_, 4);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2120_ = v___x_2113_;
v_isShared_2121_ = v_isSharedCheck_2320_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_diag_2118_);
lean_inc(v_postponed_2117_);
lean_inc(v_zetaDeltaFVarIds_2116_);
lean_inc(v_cache_2114_);
lean_inc(v_mctx_2115_);
lean_dec(v___x_2113_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2320_;
goto v_resetjp_2119_;
}
v___jp_2073_:
{
if (v___y_2075_ == 0)
{
lean_object* v___x_2076_; 
lean_del_object(v___x_2071_);
v___x_2076_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2069_, v_a_2064_, v_a_2066_);
lean_dec(v_a_2069_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v___x_2076_, 0);
lean_dec(v_unused_2084_);
v___x_2078_ = v___x_2076_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_dec(v___x_2076_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 1);
lean_ctor_set(v___x_2078_, 0, v___y_2074_);
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___y_2074_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v___y_2074_);
v_a_2085_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2076_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2076_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v___x_2094_; 
lean_dec(v_a_2069_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 1);
lean_ctor_set(v___x_2071_, 0, v___y_2074_);
v___x_2094_ = v___x_2071_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___y_2074_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
v___jp_2096_:
{
uint8_t v___x_2098_; 
v___x_2098_ = l_Lean_Exception_isInterrupt(v_a_2097_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; 
lean_inc_ref(v_a_2097_);
v___x_2099_ = l_Lean_Exception_isRuntime(v_a_2097_);
v___y_2074_ = v_a_2097_;
v___y_2075_ = v___x_2099_;
goto v___jp_2073_;
}
else
{
v___y_2074_ = v_a_2097_;
v___y_2075_ = v___x_2098_;
goto v___jp_2073_;
}
}
v___jp_2100_:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2069_, v_a_2064_, v_a_2066_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2110_; 
lean_del_object(v___x_2071_);
lean_dec(v_a_2069_);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v___x_2102_, 0);
lean_dec(v_unused_2111_);
v___x_2104_ = v___x_2102_;
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
else
{
lean_dec(v___x_2102_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_box(v_a_2101_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2106_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2112_; 
v_a_2112_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2102_, 1);
v_a_2097_ = v_a_2112_;
goto v___jp_2096_;
}
}
v_resetjp_2119_:
{
lean_object* v_inferType_2122_; lean_object* v_funInfo_2123_; lean_object* v_synthInstance_2124_; lean_object* v_whnf_2125_; lean_object* v_defEqPerm_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2318_; 
v_inferType_2122_ = lean_ctor_get(v_cache_2114_, 0);
v_funInfo_2123_ = lean_ctor_get(v_cache_2114_, 1);
v_synthInstance_2124_ = lean_ctor_get(v_cache_2114_, 2);
v_whnf_2125_ = lean_ctor_get(v_cache_2114_, 3);
v_defEqPerm_2126_ = lean_ctor_get(v_cache_2114_, 5);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_cache_2114_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; 
v_unused_2319_ = lean_ctor_get(v_cache_2114_, 4);
lean_dec(v_unused_2319_);
v___x_2128_ = v_cache_2114_;
v_isShared_2129_ = v_isSharedCheck_2318_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_defEqPerm_2126_);
lean_inc(v_whnf_2125_);
lean_inc(v_synthInstance_2124_);
lean_inc(v_funInfo_2123_);
lean_inc(v_inferType_2122_);
lean_dec(v_cache_2114_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2318_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 4, v___x_2130_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_inferType_2122_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_funInfo_2123_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_synthInstance_2124_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_whnf_2125_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2317_, 5, v_defEqPerm_2126_);
v___x_2132_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v___x_2132_);
v___x_2134_ = v___x_2120_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_mctx_2115_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v_zetaDeltaFVarIds_2116_);
lean_ctor_set(v_reuseFailAlloc_2316_, 3, v_postponed_2117_);
lean_ctor_set(v_reuseFailAlloc_2316_, 4, v_diag_2118_);
v___x_2134_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_st_ref_put(v_a_2064_, v___x_2134_);
v___x_2136_ = l_Lean_Meta_getResetPostponed___redArg(v_a_2064_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; uint8_t v_a_2139_; lean_object* v___x_2180_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
lean_inc(v_candidate_2059_);
v___x_2180_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_candidate_2059_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = l_Lean_ConstantInfo_levelParams(v_a_2181_);
v___x_2183_ = lean_box(0);
v___x_2184_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v___x_2182_, v___x_2183_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = 0;
v___x_2187_ = l_Lean_Core_instantiateValueLevelParams(v_a_2181_, v_a_2185_, v___x_2186_, v_a_2065_, v_a_2066_);
lean_dec(v_a_2181_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v___x_2189_ = lean_box(0);
v___x_2190_ = l_Lean_Meta_lambdaMetaTelescope(v_a_2188_, v___x_2189_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec(v_a_2188_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v_snd_2192_; lean_object* v_fst_2193_; lean_object* v_fst_2194_; lean_object* v_snd_2195_; lean_object* v___x_2196_; uint8_t v_foApprox_2197_; uint8_t v_ctxApprox_2198_; uint8_t v_quasiPatternApprox_2199_; uint8_t v_constApprox_2200_; uint8_t v_isDefEqStuckEx_2201_; uint8_t v_proofIrrelevance_2202_; uint8_t v_assignSyntheticOpaque_2203_; uint8_t v_offsetCnstrs_2204_; uint8_t v_transparency_2205_; uint8_t v_etaStruct_2206_; uint8_t v_univApprox_2207_; uint8_t v_iota_2208_; uint8_t v_beta_2209_; uint8_t v_proj_2210_; uint8_t v_zeta_2211_; uint8_t v_zetaDelta_2212_; uint8_t v_zetaUnused_2213_; uint8_t v_zetaHave_2214_; uint8_t v_canUnfoldPredicateConfig_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2303_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v_snd_2192_ = lean_ctor_get(v_a_2191_, 1);
lean_inc(v_snd_2192_);
v_fst_2193_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_fst_2193_);
lean_dec(v_a_2191_);
v_fst_2194_ = lean_ctor_get(v_snd_2192_, 0);
lean_inc(v_fst_2194_);
v_snd_2195_ = lean_ctor_get(v_snd_2192_, 1);
lean_inc(v_snd_2195_);
lean_dec(v_snd_2192_);
v___x_2196_ = l_Lean_Meta_Context_config(v_a_2063_);
v_foApprox_2197_ = lean_ctor_get_uint8(v___x_2196_, 0);
v_ctxApprox_2198_ = lean_ctor_get_uint8(v___x_2196_, 1);
v_quasiPatternApprox_2199_ = lean_ctor_get_uint8(v___x_2196_, 2);
v_constApprox_2200_ = lean_ctor_get_uint8(v___x_2196_, 3);
v_isDefEqStuckEx_2201_ = lean_ctor_get_uint8(v___x_2196_, 4);
v_proofIrrelevance_2202_ = lean_ctor_get_uint8(v___x_2196_, 6);
v_assignSyntheticOpaque_2203_ = lean_ctor_get_uint8(v___x_2196_, 7);
v_offsetCnstrs_2204_ = lean_ctor_get_uint8(v___x_2196_, 8);
v_transparency_2205_ = lean_ctor_get_uint8(v___x_2196_, 9);
v_etaStruct_2206_ = lean_ctor_get_uint8(v___x_2196_, 10);
v_univApprox_2207_ = lean_ctor_get_uint8(v___x_2196_, 11);
v_iota_2208_ = lean_ctor_get_uint8(v___x_2196_, 12);
v_beta_2209_ = lean_ctor_get_uint8(v___x_2196_, 13);
v_proj_2210_ = lean_ctor_get_uint8(v___x_2196_, 14);
v_zeta_2211_ = lean_ctor_get_uint8(v___x_2196_, 15);
v_zetaDelta_2212_ = lean_ctor_get_uint8(v___x_2196_, 16);
v_zetaUnused_2213_ = lean_ctor_get_uint8(v___x_2196_, 17);
v_zetaHave_2214_ = lean_ctor_get_uint8(v___x_2196_, 18);
v_canUnfoldPredicateConfig_2215_ = lean_ctor_get_uint8(v___x_2196_, 19);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2217_ = v___x_2196_;
v_isShared_2218_ = v_isSharedCheck_2303_;
goto v_resetjp_2216_;
}
else
{
lean_dec(v___x_2196_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2303_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; 
v___x_2219_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_2195_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_dec_ref_known(v___x_2219_, 1);
lean_del_object(v___x_2217_);
lean_dec(v_fst_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_a_2137_);
lean_dec_ref(v_s_2061_);
lean_dec_ref(v_t_2060_);
lean_dec(v_candidate_2059_);
v_a_2101_ = v___x_2186_;
goto v___jp_2100_;
}
else
{
lean_object* v_a_2220_; uint8_t v_trackZetaDelta_2221_; lean_object* v_zetaDeltaSet_2222_; lean_object* v_lctx_2223_; lean_object* v_localInstances_2224_; lean_object* v_defEqCtx_x3f_2225_; lean_object* v_synthPendingDepth_2226_; lean_object* v_customCanUnfoldPredicate_x3f_2227_; uint8_t v_univApprox_2228_; uint8_t v_inTypeClassResolution_2229_; uint8_t v_cacheInferType_2230_; lean_object* v_pattern_2231_; lean_object* v_constraints_2232_; uint8_t v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v_lhs_2265_; lean_object* v_rhs_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2302_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v_trackZetaDelta_2221_ = lean_ctor_get_uint8(v_a_2063_, sizeof(void*)*7);
v_zetaDeltaSet_2222_ = lean_ctor_get(v_a_2063_, 1);
v_lctx_2223_ = lean_ctor_get(v_a_2063_, 2);
v_localInstances_2224_ = lean_ctor_get(v_a_2063_, 3);
v_defEqCtx_x3f_2225_ = lean_ctor_get(v_a_2063_, 4);
v_synthPendingDepth_2226_ = lean_ctor_get(v_a_2063_, 5);
v_customCanUnfoldPredicate_x3f_2227_ = lean_ctor_get(v_a_2063_, 6);
v_univApprox_2228_ = lean_ctor_get_uint8(v_a_2063_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2229_ = lean_ctor_get_uint8(v_a_2063_, sizeof(void*)*7 + 2);
v_cacheInferType_2230_ = lean_ctor_get_uint8(v_a_2063_, sizeof(void*)*7 + 3);
v_pattern_2231_ = lean_ctor_get(v_a_2220_, 0);
lean_inc_ref(v_pattern_2231_);
v_constraints_2232_ = lean_ctor_get(v_a_2220_, 1);
lean_inc(v_constraints_2232_);
lean_dec(v_a_2220_);
v_lhs_2265_ = lean_ctor_get(v_pattern_2231_, 0);
v_rhs_2266_ = lean_ctor_get(v_pattern_2231_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_pattern_2231_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2268_ = v_pattern_2231_;
v_isShared_2269_ = v_isSharedCheck_2302_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_rhs_2266_);
lean_inc(v_lhs_2265_);
lean_dec(v_pattern_2231_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2302_;
goto v_resetjp_2267_;
}
v___jp_2233_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2240_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_constraints_2232_, v___x_2239_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v_constraints_2232_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v_fst_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2262_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v_fst_2242_ = lean_ctor_get(v_a_2241_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_a_2241_);
if (v_isSharedCheck_2262_ == 0)
{
lean_object* v_unused_2263_; 
v_unused_2263_ = lean_ctor_get(v_a_2241_, 1);
lean_dec(v_unused_2263_);
v___x_2244_ = v_a_2241_;
v_isShared_2245_ = v_isSharedCheck_2262_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_fst_2242_);
lean_dec(v_a_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2262_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
if (lean_obj_tag(v_fst_2242_) == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = lean_array_get_size(v_fst_2194_);
v___x_2248_ = l_Array_toSubarray___redArg(v_fst_2194_, v___x_2246_, v___x_2247_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 1, v___x_2248_);
lean_ctor_set(v___x_2244_, 0, v___x_2189_);
v___x_2250_ = v___x_2244_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
size_t v_sz_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v_sz_2251_ = lean_array_size(v_fst_2193_);
v___x_2252_ = ((size_t)0ULL);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_fst_2193_, v_sz_2251_, v___x_2252_, v___x_2250_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v_fst_2193_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v_fst_2255_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v_fst_2255_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_fst_2255_);
lean_dec(v_a_2254_);
if (lean_obj_tag(v_fst_2255_) == 0)
{
v_a_2139_ = v___y_2234_;
goto v___jp_2138_;
}
else
{
lean_object* v_val_2256_; uint8_t v___x_2257_; 
v_val_2256_ = lean_ctor_get(v_fst_2255_, 0);
lean_inc(v_val_2256_);
lean_dec_ref_known(v_fst_2255_, 1);
v___x_2257_ = lean_unbox(v_val_2256_);
lean_dec(v_val_2256_);
v_a_2139_ = v___x_2257_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_a_2258_; 
lean_dec(v_a_2137_);
v_a_2258_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2253_, 1);
v_a_2097_ = v_a_2258_;
goto v___jp_2096_;
}
}
}
else
{
lean_object* v_val_2260_; uint8_t v___x_2261_; 
lean_del_object(v___x_2244_);
lean_dec(v_fst_2194_);
lean_dec(v_fst_2193_);
v_val_2260_ = lean_ctor_get(v_fst_2242_, 0);
lean_inc(v_val_2260_);
lean_dec_ref_known(v_fst_2242_, 1);
v___x_2261_ = lean_unbox(v_val_2260_);
lean_dec(v_val_2260_);
v_a_2139_ = v___x_2261_;
goto v___jp_2138_;
}
}
}
else
{
lean_object* v_a_2264_; 
lean_dec(v_fst_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_a_2137_);
v_a_2264_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v___x_2240_, 1);
v_a_2097_ = v_a_2264_;
goto v___jp_2096_;
}
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2218_ == 0)
{
v___x_2271_ = v___x_2217_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 0, v_foApprox_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 1, v_ctxApprox_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 2, v_quasiPatternApprox_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 3, v_constApprox_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 4, v_isDefEqStuckEx_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 6, v_proofIrrelevance_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 7, v_assignSyntheticOpaque_2203_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 8, v_offsetCnstrs_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 9, v_transparency_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 10, v_etaStruct_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 11, v_univApprox_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 12, v_iota_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 13, v_beta_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 14, v_proj_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 15, v_zeta_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 16, v_zetaDelta_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 17, v_zetaUnused_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 18, v_zetaHave_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, 19, v_canUnfoldPredicateConfig_2215_);
v___x_2271_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
uint64_t v___x_2272_; lean_object* v_cls_2273_; lean_object* v___y_2275_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_ctor_set_uint8(v___x_2271_, 5, v___x_2186_);
v___x_2272_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2271_);
v_cls_2273_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2295_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2295_, 0, v___x_2271_);
lean_ctor_set_uint64(v___x_2295_, sizeof(void*)*1, v___x_2272_);
lean_inc(v_customCanUnfoldPredicate_x3f_2227_);
lean_inc(v_synthPendingDepth_2226_);
lean_inc(v_defEqCtx_x3f_2225_);
lean_inc_ref(v_localInstances_2224_);
lean_inc_ref(v_lctx_2223_);
lean_inc(v_zetaDeltaSet_2222_);
v___x_2296_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v_zetaDeltaSet_2222_);
lean_ctor_set(v___x_2296_, 2, v_lctx_2223_);
lean_ctor_set(v___x_2296_, 3, v_localInstances_2224_);
lean_ctor_set(v___x_2296_, 4, v_defEqCtx_x3f_2225_);
lean_ctor_set(v___x_2296_, 5, v_synthPendingDepth_2226_);
lean_ctor_set(v___x_2296_, 6, v_customCanUnfoldPredicate_x3f_2227_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*7, v_trackZetaDelta_2221_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*7 + 1, v_univApprox_2228_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2229_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*7 + 3, v_cacheInferType_2230_);
v___x_2297_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_lhs_2265_, v_t_2060_, v___x_2296_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; uint8_t v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
v___x_2299_ = lean_unbox(v_a_2298_);
lean_dec(v_a_2298_);
if (v___x_2299_ == 0)
{
lean_dec_ref_known(v___x_2296_, 7);
lean_dec_ref(v_rhs_2266_);
lean_dec_ref(v_s_2061_);
v___y_2275_ = v___x_2297_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2300_; 
lean_dec_ref_known(v___x_2297_, 1);
v___x_2300_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_rhs_2266_, v_s_2061_, v___x_2296_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec_ref_known(v___x_2296_, 7);
v___y_2275_ = v___x_2300_;
goto v___jp_2274_;
}
}
else
{
lean_dec_ref_known(v___x_2296_, 7);
lean_dec_ref(v_rhs_2266_);
lean_dec_ref(v_s_2061_);
v___y_2275_ = v___x_2297_;
goto v___jp_2274_;
}
v___jp_2274_:
{
if (lean_obj_tag(v___y_2275_) == 0)
{
lean_object* v_a_2276_; uint8_t v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___y_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___y_2275_, 1);
v___x_2277_ = lean_unbox(v_a_2276_);
if (v___x_2277_ == 0)
{
lean_dec(v_a_2276_);
lean_del_object(v___x_2268_);
lean_dec(v_constraints_2232_);
lean_dec(v_fst_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_a_2137_);
lean_dec(v_candidate_2059_);
v_a_2101_ = v___x_2186_;
goto v___jp_2100_;
}
else
{
lean_object* v_toCold_2278_; lean_object* v_options_2279_; uint8_t v_hasTrace_2280_; 
v_toCold_2278_ = lean_ctor_get(v_a_2065_, 0);
v_options_2279_ = lean_ctor_get(v_toCold_2278_, 2);
v_hasTrace_2280_ = lean_ctor_get_uint8(v_options_2279_, sizeof(void*)*1);
if (v_hasTrace_2280_ == 0)
{
uint8_t v___x_2281_; 
lean_del_object(v___x_2268_);
lean_dec(v_candidate_2059_);
v___x_2281_ = lean_unbox(v_a_2276_);
lean_dec(v_a_2276_);
v___y_2234_ = v___x_2281_;
v___y_2235_ = v_a_2063_;
v___y_2236_ = v_a_2064_;
v___y_2237_ = v_a_2065_;
v___y_2238_ = v_a_2066_;
goto v___jp_2233_;
}
else
{
lean_object* v_inheritedTraceOptions_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_inheritedTraceOptions_2282_ = lean_ctor_get(v_toCold_2278_, 11);
v___x_2283_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2284_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2282_, v_options_2279_, v___x_2283_);
if (v___x_2284_ == 0)
{
uint8_t v___x_2285_; 
lean_del_object(v___x_2268_);
lean_dec(v_candidate_2059_);
v___x_2285_ = lean_unbox(v_a_2276_);
lean_dec(v_a_2276_);
v___y_2234_ = v___x_2285_;
v___y_2235_ = v_a_2063_;
v___y_2236_ = v_a_2064_;
v___y_2237_ = v_a_2065_;
v___y_2238_ = v_a_2066_;
goto v___jp_2233_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2286_ = l_Lean_MessageData_ofName(v_candidate_2059_);
v___x_2287_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10);
if (v_isShared_2269_ == 0)
{
lean_ctor_set_tag(v___x_2268_, 7);
lean_ctor_set(v___x_2268_, 1, v___x_2287_);
lean_ctor_set(v___x_2268_, 0, v___x_2286_);
v___x_2289_ = v___x_2268_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2273_, v___x_2289_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2290_) == 0)
{
uint8_t v___x_2291_; 
lean_dec_ref_known(v___x_2290_, 1);
v___x_2291_ = lean_unbox(v_a_2276_);
lean_dec(v_a_2276_);
v___y_2234_ = v___x_2291_;
v___y_2235_ = v_a_2063_;
v___y_2236_ = v_a_2064_;
v___y_2237_ = v_a_2065_;
v___y_2238_ = v_a_2066_;
goto v___jp_2233_;
}
else
{
lean_object* v_a_2292_; 
lean_dec(v_a_2276_);
lean_dec(v_constraints_2232_);
lean_dec(v_fst_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_a_2137_);
v_a_2292_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2290_, 1);
v_a_2097_ = v_a_2292_;
goto v___jp_2096_;
}
}
}
}
}
}
else
{
lean_object* v_a_2294_; 
lean_del_object(v___x_2268_);
lean_dec(v_constraints_2232_);
lean_dec(v_fst_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_a_2137_);
lean_dec(v_candidate_2059_);
v_a_2294_ = lean_ctor_get(v___y_2275_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___y_2275_, 1);
v_a_2097_ = v_a_2294_;
goto v___jp_2096_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2304_; 
lean_dec(v_a_2137_);
lean_dec_ref(v_s_2061_);
lean_dec_ref(v_t_2060_);
lean_dec(v_candidate_2059_);
v_a_2304_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2190_, 1);
v_a_2097_ = v_a_2304_;
goto v___jp_2096_;
}
}
else
{
lean_object* v_a_2305_; 
lean_dec(v_a_2137_);
lean_dec_ref(v_s_2061_);
lean_dec_ref(v_t_2060_);
lean_dec(v_candidate_2059_);
v_a_2305_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2187_, 1);
v_a_2097_ = v_a_2305_;
goto v___jp_2096_;
}
}
else
{
lean_object* v_a_2306_; 
lean_dec(v_a_2181_);
lean_dec(v_a_2137_);
lean_dec_ref(v_s_2061_);
lean_dec_ref(v_t_2060_);
lean_dec(v_candidate_2059_);
v_a_2306_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2184_, 1);
v_a_2097_ = v_a_2306_;
goto v___jp_2096_;
}
}
else
{
lean_object* v_a_2307_; 
lean_dec(v_a_2137_);
lean_dec_ref(v_s_2061_);
lean_dec_ref(v_t_2060_);
lean_dec(v_candidate_2059_);
v_a_2307_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2180_, 1);
v_a_2097_ = v_a_2307_;
goto v___jp_2096_;
}
v___jp_2138_:
{
if (v_a_2139_ == 0)
{
lean_dec(v_a_2137_);
v_a_2101_ = v_a_2139_;
goto v___jp_2100_;
}
else
{
uint8_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = 0;
v___x_2141_ = l_Lean_Meta_processPostponed(v_mayPostpone_2062_, v___x_2140_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2178_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2178_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2178_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
uint8_t v___x_2146_; 
v___x_2146_ = lean_unbox(v_a_2142_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_del_object(v___x_2144_);
lean_dec(v_a_2142_);
lean_dec(v_a_2137_);
v___x_2147_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2069_, v_a_2064_, v_a_2066_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2155_; 
lean_del_object(v___x_2071_);
lean_dec(v_a_2069_);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v___x_2147_, 0);
lean_dec(v_unused_2156_);
v___x_2149_ = v___x_2147_;
v_isShared_2150_ = v_isSharedCheck_2155_;
goto v_resetjp_2148_;
}
else
{
lean_dec(v___x_2147_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2155_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = lean_box(v___x_2140_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2151_);
v___x_2153_ = v___x_2149_;
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
else
{
lean_object* v_a_2157_; 
v_a_2157_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2147_, 1);
v_a_2097_ = v_a_2157_;
goto v___jp_2096_;
}
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v_postponed_2160_; lean_object* v_mctx_2161_; lean_object* v_cache_2162_; lean_object* v_zetaDeltaFVarIds_2163_; lean_object* v_diag_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2176_; 
lean_del_object(v___x_2071_);
lean_dec(v_a_2069_);
v___x_2158_ = lean_st_ref_get(v_a_2064_);
v___x_2159_ = lean_st_ref_take(v_a_2064_);
v_postponed_2160_ = lean_ctor_get(v___x_2158_, 3);
lean_inc_ref(v_postponed_2160_);
lean_dec(v___x_2158_);
v_mctx_2161_ = lean_ctor_get(v___x_2159_, 0);
v_cache_2162_ = lean_ctor_get(v___x_2159_, 1);
v_zetaDeltaFVarIds_2163_ = lean_ctor_get(v___x_2159_, 2);
v_diag_2164_ = lean_ctor_get(v___x_2159_, 4);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; 
v_unused_2177_ = lean_ctor_get(v___x_2159_, 3);
lean_dec(v_unused_2177_);
v___x_2166_ = v___x_2159_;
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_diag_2164_);
lean_inc(v_zetaDeltaFVarIds_2163_);
lean_inc(v_cache_2162_);
lean_inc(v_mctx_2161_);
lean_dec(v___x_2159_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = l_Lean_PersistentArray_append___redArg(v_a_2137_, v_postponed_2160_);
lean_dec_ref(v_postponed_2160_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 3, v___x_2168_);
v___x_2170_ = v___x_2166_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_mctx_2161_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_cache_2162_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_zetaDeltaFVarIds_2163_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_diag_2164_);
v___x_2170_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_st_ref_put(v_a_2064_, v___x_2170_);
if (v_isShared_2145_ == 0)
{
v___x_2173_ = v___x_2144_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2142_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
}
else
{
lean_object* v_a_2179_; 
lean_dec(v_a_2137_);
v_a_2179_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2141_, 1);
v_a_2097_ = v_a_2179_;
goto v___jp_2096_;
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_del_object(v___x_2071_);
lean_dec(v_a_2069_);
lean_dec_ref(v_s_2061_);
lean_dec_ref(v_t_2060_);
lean_dec(v_candidate_2059_);
v_a_2308_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2136_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2136_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
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
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec_ref(v_s_2061_);
lean_dec_ref(v_t_2060_);
lean_dec(v_candidate_2059_);
v_a_2322_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2068_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2068_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object* v_candidate_2330_, lean_object* v_t_2331_, lean_object* v_s_2332_, lean_object* v_mayPostpone_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
uint8_t v_mayPostpone_boxed_2339_; lean_object* v_res_2340_; 
v_mayPostpone_boxed_2339_ = lean_unbox(v_mayPostpone_2333_);
v_res_2340_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2330_, v_t_2331_, v_s_2332_, v_mayPostpone_boxed_2339_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
return v_res_2340_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = lean_unsigned_to_nat(32u);
v___x_2342_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2344_ = ((size_t)5ULL);
v___x_2345_ = lean_unsigned_to_nat(0u);
v___x_2346_ = lean_unsigned_to_nat(32u);
v___x_2347_ = lean_mk_empty_array_with_capacity(v___x_2346_);
v___x_2348_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0);
v___x_2349_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
lean_ctor_set(v___x_2349_, 1, v___x_2347_);
lean_ctor_set(v___x_2349_, 2, v___x_2345_);
lean_ctor_set(v___x_2349_, 3, v___x_2345_);
lean_ctor_set_usize(v___x_2349_, 4, v___x_2344_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v_traceState_2353_; lean_object* v_traces_2354_; lean_object* v___x_2355_; lean_object* v_traceState_2356_; lean_object* v_env_2357_; lean_object* v_nextMacroScope_2358_; lean_object* v_ngen_2359_; lean_object* v_auxDeclNGen_2360_; lean_object* v_cache_2361_; lean_object* v_messages_2362_; lean_object* v_infoState_2363_; lean_object* v_snapshotTasks_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2383_; 
v___x_2352_ = lean_st_ref_get(v___y_2350_);
v_traceState_2353_ = lean_ctor_get(v___x_2352_, 4);
lean_inc_ref(v_traceState_2353_);
lean_dec(v___x_2352_);
v_traces_2354_ = lean_ctor_get(v_traceState_2353_, 0);
lean_inc_ref(v_traces_2354_);
lean_dec_ref(v_traceState_2353_);
v___x_2355_ = lean_st_ref_take(v___y_2350_);
v_traceState_2356_ = lean_ctor_get(v___x_2355_, 4);
v_env_2357_ = lean_ctor_get(v___x_2355_, 0);
v_nextMacroScope_2358_ = lean_ctor_get(v___x_2355_, 1);
v_ngen_2359_ = lean_ctor_get(v___x_2355_, 2);
v_auxDeclNGen_2360_ = lean_ctor_get(v___x_2355_, 3);
v_cache_2361_ = lean_ctor_get(v___x_2355_, 5);
v_messages_2362_ = lean_ctor_get(v___x_2355_, 6);
v_infoState_2363_ = lean_ctor_get(v___x_2355_, 7);
v_snapshotTasks_2364_ = lean_ctor_get(v___x_2355_, 8);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2366_ = v___x_2355_;
v_isShared_2367_ = v_isSharedCheck_2383_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_snapshotTasks_2364_);
lean_inc(v_infoState_2363_);
lean_inc(v_messages_2362_);
lean_inc(v_cache_2361_);
lean_inc(v_traceState_2356_);
lean_inc(v_auxDeclNGen_2360_);
lean_inc(v_ngen_2359_);
lean_inc(v_nextMacroScope_2358_);
lean_inc(v_env_2357_);
lean_dec(v___x_2355_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2383_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
uint64_t v_tid_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2381_; 
v_tid_2368_ = lean_ctor_get_uint64(v_traceState_2356_, sizeof(void*)*1);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_traceState_2356_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; 
v_unused_2382_ = lean_ctor_get(v_traceState_2356_, 0);
lean_dec(v_unused_2382_);
v___x_2370_ = v_traceState_2356_;
v_isShared_2371_ = v_isSharedCheck_2381_;
goto v_resetjp_2369_;
}
else
{
lean_dec(v_traceState_2356_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2381_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2372_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2372_);
v___x_2374_ = v___x_2370_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2372_);
lean_ctor_set_uint64(v_reuseFailAlloc_2380_, sizeof(void*)*1, v_tid_2368_);
v___x_2374_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 4, v___x_2374_);
v___x_2376_ = v___x_2366_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_env_2357_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_nextMacroScope_2358_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_ngen_2359_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v_auxDeclNGen_2360_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2379_, 5, v_cache_2361_);
lean_ctor_set(v_reuseFailAlloc_2379_, 6, v_messages_2362_);
lean_ctor_set(v_reuseFailAlloc_2379_, 7, v_infoState_2363_);
lean_ctor_set(v_reuseFailAlloc_2379_, 8, v_snapshotTasks_2364_);
v___x_2376_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_st_ref_put(v___y_2350_, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_traces_2354_);
return v___x_2378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___boxed(lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2384_);
lean_dec(v___y_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object* v_opts_2399_, lean_object* v_opt_2400_){
_start:
{
lean_object* v_name_2401_; lean_object* v_defValue_2402_; lean_object* v_map_2403_; lean_object* v___x_2404_; 
v_name_2401_ = lean_ctor_get(v_opt_2400_, 0);
v_defValue_2402_ = lean_ctor_get(v_opt_2400_, 1);
v_map_2403_ = lean_ctor_get(v_opts_2399_, 0);
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2403_, v_name_2401_);
if (lean_obj_tag(v___x_2404_) == 0)
{
uint8_t v___x_2405_; 
v___x_2405_ = lean_unbox(v_defValue_2402_);
return v___x_2405_;
}
else
{
lean_object* v_val_2406_; 
v_val_2406_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_val_2406_);
lean_dec_ref_known(v___x_2404_, 1);
if (lean_obj_tag(v_val_2406_) == 1)
{
uint8_t v_v_2407_; 
v_v_2407_ = lean_ctor_get_uint8(v_val_2406_, 0);
lean_dec_ref_known(v_val_2406_, 0);
return v_v_2407_;
}
else
{
uint8_t v___x_2408_; 
lean_dec(v_val_2406_);
v___x_2408_ = lean_unbox(v_defValue_2402_);
return v___x_2408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object* v_opts_2409_, lean_object* v_opt_2410_){
_start:
{
uint8_t v_res_2411_; lean_object* v_r_2412_; 
v_res_2411_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2409_, v_opt_2410_);
lean_dec_ref(v_opt_2410_);
lean_dec_ref(v_opts_2409_);
v_r_2412_ = lean_box(v_res_2411_);
return v_r_2412_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0));
v___x_2415_ = l_Lean_stringToMessageData(v___x_2414_);
return v___x_2415_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2));
v___x_2418_ = l_Lean_stringToMessageData(v___x_2417_);
return v___x_2418_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4));
v___x_2421_ = l_Lean_stringToMessageData(v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object* v_candidate_2422_, lean_object* v_t_2423_, lean_object* v_s_2424_, lean_object* v_x_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2431_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1);
v___x_2432_ = l_Lean_MessageData_ofName(v_candidate_2422_);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = l_Lean_MessageData_ofExpr(v_t_2423_);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = l_Lean_MessageData_ofExpr(v_s_2424_);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object* v_candidate_2443_, lean_object* v_t_2444_, lean_object* v_s_2445_, lean_object* v_x_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(v_candidate_2443_, v_t_2444_, v_s_2445_, v_x_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v_x_2446_);
return v_res_2452_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(lean_object* v_e_2453_){
_start:
{
if (lean_obj_tag(v_e_2453_) == 0)
{
uint8_t v___x_2454_; 
v___x_2454_ = 2;
return v___x_2454_;
}
else
{
lean_object* v_a_2455_; uint8_t v___x_2456_; 
v_a_2455_ = lean_ctor_get(v_e_2453_, 0);
v___x_2456_ = lean_unbox(v_a_2455_);
if (v___x_2456_ == 0)
{
uint8_t v___x_2457_; 
v___x_2457_ = 1;
return v___x_2457_;
}
else
{
uint8_t v___x_2458_; 
v___x_2458_ = 0;
return v___x_2458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(lean_object* v_e_2459_){
_start:
{
uint8_t v_res_2460_; lean_object* v_r_2461_; 
v_res_2460_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_e_2459_);
lean_dec_ref(v_e_2459_);
v_r_2461_ = lean_box(v_res_2460_);
return v_r_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(size_t v_sz_2462_, size_t v_i_2463_, lean_object* v_bs_2464_){
_start:
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_usize_dec_lt(v_i_2463_, v_sz_2462_);
if (v___x_2465_ == 0)
{
return v_bs_2464_;
}
else
{
lean_object* v_v_2466_; lean_object* v_msg_2467_; lean_object* v___x_2468_; lean_object* v_bs_x27_2469_; size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; 
v_v_2466_ = lean_array_uget_borrowed(v_bs_2464_, v_i_2463_);
v_msg_2467_ = lean_ctor_get(v_v_2466_, 1);
lean_inc_ref(v_msg_2467_);
v___x_2468_ = lean_unsigned_to_nat(0u);
v_bs_x27_2469_ = lean_array_uset(v_bs_2464_, v_i_2463_, v___x_2468_);
v___x_2470_ = ((size_t)1ULL);
v___x_2471_ = lean_usize_add(v_i_2463_, v___x_2470_);
v___x_2472_ = lean_array_uset(v_bs_x27_2469_, v_i_2463_, v_msg_2467_);
v_i_2463_ = v___x_2471_;
v_bs_2464_ = v___x_2472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8___boxed(lean_object* v_sz_2474_, lean_object* v_i_2475_, lean_object* v_bs_2476_){
_start:
{
size_t v_sz_boxed_2477_; size_t v_i_boxed_2478_; lean_object* v_res_2479_; 
v_sz_boxed_2477_ = lean_unbox_usize(v_sz_2474_);
lean_dec(v_sz_2474_);
v_i_boxed_2478_ = lean_unbox_usize(v_i_2475_);
lean_dec(v_i_2475_);
v_res_2479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(v_sz_boxed_2477_, v_i_boxed_2478_, v_bs_2476_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(lean_object* v_oldTraces_2480_, lean_object* v_data_2481_, lean_object* v_ref_2482_, lean_object* v_msg_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_toCold_2489_; lean_object* v_currRecDepth_2490_; lean_object* v_ref_2491_; uint8_t v_diag_2492_; uint8_t v_suppressElabErrors_2493_; lean_object* v___x_2494_; lean_object* v_traceState_2495_; lean_object* v_traces_2496_; lean_object* v_ref_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; lean_object* v_msg_2503_; lean_object* v___x_2504_; lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2542_; 
v_toCold_2489_ = lean_ctor_get(v___y_2486_, 0);
v_currRecDepth_2490_ = lean_ctor_get(v___y_2486_, 1);
v_ref_2491_ = lean_ctor_get(v___y_2486_, 2);
v_diag_2492_ = lean_ctor_get_uint8(v___y_2486_, sizeof(void*)*3);
v_suppressElabErrors_2493_ = lean_ctor_get_uint8(v___y_2486_, sizeof(void*)*3 + 1);
v___x_2494_ = lean_st_ref_get(v___y_2487_);
v_traceState_2495_ = lean_ctor_get(v___x_2494_, 4);
lean_inc_ref(v_traceState_2495_);
lean_dec(v___x_2494_);
v_traces_2496_ = lean_ctor_get(v_traceState_2495_, 0);
lean_inc_ref(v_traces_2496_);
lean_dec_ref(v_traceState_2495_);
v_ref_2497_ = l_Lean_replaceRef(v_ref_2482_, v_ref_2491_);
lean_inc(v_currRecDepth_2490_);
lean_inc_ref(v_toCold_2489_);
v___x_2498_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2498_, 0, v_toCold_2489_);
lean_ctor_set(v___x_2498_, 1, v_currRecDepth_2490_);
lean_ctor_set(v___x_2498_, 2, v_ref_2497_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3, v_diag_2492_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 1, v_suppressElabErrors_2493_);
v___x_2499_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2496_);
lean_dec_ref(v_traces_2496_);
v_sz_2500_ = lean_array_size(v___x_2499_);
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(v_sz_2500_, v___x_2501_, v___x_2499_);
v_msg_2503_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2503_, 0, v_data_2481_);
lean_ctor_set(v_msg_2503_, 1, v_msg_2483_);
lean_ctor_set(v_msg_2503_, 2, v___x_2502_);
v___x_2504_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2503_, v___y_2484_, v___y_2485_, v___x_2498_, v___y_2487_);
lean_dec_ref_known(v___x_2498_, 3);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2542_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2542_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v_traceState_2510_; lean_object* v_env_2511_; lean_object* v_nextMacroScope_2512_; lean_object* v_ngen_2513_; lean_object* v_auxDeclNGen_2514_; lean_object* v_cache_2515_; lean_object* v_messages_2516_; lean_object* v_infoState_2517_; lean_object* v_snapshotTasks_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2541_; 
v___x_2509_ = lean_st_ref_take(v___y_2487_);
v_traceState_2510_ = lean_ctor_get(v___x_2509_, 4);
v_env_2511_ = lean_ctor_get(v___x_2509_, 0);
v_nextMacroScope_2512_ = lean_ctor_get(v___x_2509_, 1);
v_ngen_2513_ = lean_ctor_get(v___x_2509_, 2);
v_auxDeclNGen_2514_ = lean_ctor_get(v___x_2509_, 3);
v_cache_2515_ = lean_ctor_get(v___x_2509_, 5);
v_messages_2516_ = lean_ctor_get(v___x_2509_, 6);
v_infoState_2517_ = lean_ctor_get(v___x_2509_, 7);
v_snapshotTasks_2518_ = lean_ctor_get(v___x_2509_, 8);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2520_ = v___x_2509_;
v_isShared_2521_ = v_isSharedCheck_2541_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_snapshotTasks_2518_);
lean_inc(v_infoState_2517_);
lean_inc(v_messages_2516_);
lean_inc(v_cache_2515_);
lean_inc(v_traceState_2510_);
lean_inc(v_auxDeclNGen_2514_);
lean_inc(v_ngen_2513_);
lean_inc(v_nextMacroScope_2512_);
lean_inc(v_env_2511_);
lean_dec(v___x_2509_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2541_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
uint64_t v_tid_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2539_; 
v_tid_2522_ = lean_ctor_get_uint64(v_traceState_2510_, sizeof(void*)*1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_traceState_2510_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v_traceState_2510_, 0);
lean_dec(v_unused_2540_);
v___x_2524_ = v_traceState_2510_;
v_isShared_2525_ = v_isSharedCheck_2539_;
goto v_resetjp_2523_;
}
else
{
lean_dec(v_traceState_2510_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2539_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_ref_2482_);
lean_ctor_set(v___x_2526_, 1, v_a_2505_);
v___x_2527_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2480_, v___x_2526_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2527_);
v___x_2529_ = v___x_2524_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2527_);
lean_ctor_set_uint64(v_reuseFailAlloc_2538_, sizeof(void*)*1, v_tid_2522_);
v___x_2529_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2531_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 4, v___x_2529_);
v___x_2531_ = v___x_2520_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_env_2511_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_nextMacroScope_2512_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_ngen_2513_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_auxDeclNGen_2514_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2537_, 5, v_cache_2515_);
lean_ctor_set(v_reuseFailAlloc_2537_, 6, v_messages_2516_);
lean_ctor_set(v_reuseFailAlloc_2537_, 7, v_infoState_2517_);
lean_ctor_set(v_reuseFailAlloc_2537_, 8, v_snapshotTasks_2518_);
v___x_2531_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = lean_st_ref_put(v___y_2487_, v___x_2531_);
v___x_2533_ = lean_box(0);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2533_);
v___x_2535_ = v___x_2507_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(lean_object* v_oldTraces_2543_, lean_object* v_data_2544_, lean_object* v_ref_2545_, lean_object* v_msg_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_oldTraces_2543_, v_data_2544_, v_ref_2545_, v_msg_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(lean_object* v_opts_2553_, lean_object* v_opt_2554_){
_start:
{
lean_object* v_name_2555_; lean_object* v_defValue_2556_; lean_object* v_map_2557_; lean_object* v___x_2558_; 
v_name_2555_ = lean_ctor_get(v_opt_2554_, 0);
v_defValue_2556_ = lean_ctor_get(v_opt_2554_, 1);
v_map_2557_ = lean_ctor_get(v_opts_2553_, 0);
v___x_2558_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2557_, v_name_2555_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_inc(v_defValue_2556_);
return v_defValue_2556_;
}
else
{
lean_object* v_val_2559_; 
v_val_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_val_2559_);
lean_dec_ref_known(v___x_2558_, 1);
if (lean_obj_tag(v_val_2559_) == 3)
{
lean_object* v_v_2560_; 
v_v_2560_ = lean_ctor_get(v_val_2559_, 0);
lean_inc(v_v_2560_);
lean_dec_ref_known(v_val_2559_, 1);
return v_v_2560_;
}
else
{
lean_dec(v_val_2559_);
lean_inc(v_defValue_2556_);
return v_defValue_2556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(lean_object* v_opts_2561_, lean_object* v_opt_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2561_, v_opt_2562_);
lean_dec_ref(v_opt_2562_);
lean_dec_ref(v_opts_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(lean_object* v_x_2564_){
_start:
{
if (lean_obj_tag(v_x_2564_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
v_a_2566_ = lean_ctor_get(v_x_2564_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_x_2564_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v_x_2564_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v_x_2564_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 1);
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_a_2574_ = lean_ctor_get(v_x_2564_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_x_2564_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v_x_2564_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v_x_2564_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set_tag(v___x_2576_, 0);
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg___boxed(lean_object* v_x_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_x_2582_);
return v_res_2584_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0));
v___x_2587_ = l_Lean_stringToMessageData(v___x_2586_);
return v___x_2587_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2(void){
_start:
{
lean_object* v___x_2588_; double v___x_2589_; 
v___x_2588_ = lean_unsigned_to_nat(1000u);
v___x_2589_ = lean_float_of_nat(v___x_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object* v_cls_2590_, uint8_t v_collapsed_2591_, lean_object* v_tag_2592_, lean_object* v_opts_2593_, uint8_t v_clsEnabled_2594_, lean_object* v_oldTraces_2595_, lean_object* v_msg_2596_, lean_object* v_resStartStop_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_fst_2603_; lean_object* v_snd_2604_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v_data_2608_; lean_object* v_fst_2619_; lean_object* v_snd_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; lean_object* v___y_2624_; lean_object* v_a_2625_; uint8_t v___y_2640_; double v___y_2671_; 
v_fst_2603_ = lean_ctor_get(v_resStartStop_2597_, 0);
lean_inc(v_fst_2603_);
v_snd_2604_ = lean_ctor_get(v_resStartStop_2597_, 1);
lean_inc(v_snd_2604_);
lean_dec_ref(v_resStartStop_2597_);
v_fst_2619_ = lean_ctor_get(v_snd_2604_, 0);
lean_inc(v_fst_2619_);
v_snd_2620_ = lean_ctor_get(v_snd_2604_, 1);
lean_inc(v_snd_2620_);
lean_dec(v_snd_2604_);
v___x_2621_ = l_Lean_trace_profiler;
v___x_2622_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2593_, v___x_2621_);
if (v___x_2622_ == 0)
{
v___y_2640_ = v___x_2622_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2677_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2593_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; double v___x_2680_; double v___x_2681_; double v___x_2682_; 
v___x_2678_ = l_Lean_trace_profiler_threshold;
v___x_2679_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2593_, v___x_2678_);
v___x_2680_ = lean_float_of_nat(v___x_2679_);
v___x_2681_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2);
v___x_2682_ = lean_float_div(v___x_2680_, v___x_2681_);
v___y_2671_ = v___x_2682_;
goto v___jp_2670_;
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; double v___x_2685_; 
v___x_2683_ = l_Lean_trace_profiler_threshold;
v___x_2684_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2593_, v___x_2683_);
v___x_2685_ = lean_float_of_nat(v___x_2684_);
v___y_2671_ = v___x_2685_;
goto v___jp_2670_;
}
}
v___jp_2605_:
{
lean_object* v___x_2609_; 
lean_inc(v___y_2607_);
v___x_2609_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_oldTraces_2595_, v_data_2608_, v___y_2607_, v___y_2606_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v___x_2610_; 
lean_dec_ref_known(v___x_2609_, 1);
v___x_2610_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_fst_2603_);
return v___x_2610_;
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v_fst_2603_);
v_a_2611_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2609_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2609_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
v___jp_2623_:
{
uint8_t v_result_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; double v___x_2629_; lean_object* v_data_2630_; 
v_result_2626_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_fst_2603_);
v___x_2627_ = lean_box(v_result_2626_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
v___x_2629_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
lean_inc_ref(v_tag_2592_);
lean_inc_ref(v___x_2628_);
lean_inc(v_cls_2590_);
v_data_2630_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2630_, 0, v_cls_2590_);
lean_ctor_set(v_data_2630_, 1, v___x_2628_);
lean_ctor_set(v_data_2630_, 2, v_tag_2592_);
lean_ctor_set_float(v_data_2630_, sizeof(void*)*3, v___x_2629_);
lean_ctor_set_float(v_data_2630_, sizeof(void*)*3 + 8, v___x_2629_);
lean_ctor_set_uint8(v_data_2630_, sizeof(void*)*3 + 16, v_collapsed_2591_);
if (v___x_2622_ == 0)
{
lean_dec_ref_known(v___x_2628_, 1);
lean_dec(v_snd_2620_);
lean_dec(v_fst_2619_);
lean_dec_ref(v_tag_2592_);
lean_dec(v_cls_2590_);
v___y_2606_ = v_a_2625_;
v___y_2607_ = v___y_2624_;
v_data_2608_ = v_data_2630_;
goto v___jp_2605_;
}
else
{
lean_object* v_data_2631_; double v___x_2632_; double v___x_2633_; 
lean_dec_ref_known(v_data_2630_, 3);
v_data_2631_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2631_, 0, v_cls_2590_);
lean_ctor_set(v_data_2631_, 1, v___x_2628_);
lean_ctor_set(v_data_2631_, 2, v_tag_2592_);
v___x_2632_ = lean_unbox_float(v_fst_2619_);
lean_dec(v_fst_2619_);
lean_ctor_set_float(v_data_2631_, sizeof(void*)*3, v___x_2632_);
v___x_2633_ = lean_unbox_float(v_snd_2620_);
lean_dec(v_snd_2620_);
lean_ctor_set_float(v_data_2631_, sizeof(void*)*3 + 8, v___x_2633_);
lean_ctor_set_uint8(v_data_2631_, sizeof(void*)*3 + 16, v_collapsed_2591_);
v___y_2606_ = v_a_2625_;
v___y_2607_ = v___y_2624_;
v_data_2608_ = v_data_2631_;
goto v___jp_2605_;
}
}
v___jp_2634_:
{
lean_object* v_ref_2635_; lean_object* v___x_2636_; 
v_ref_2635_ = lean_ctor_get(v___y_2600_, 2);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc_ref(v___y_2598_);
lean_inc(v_fst_2603_);
v___x_2636_ = lean_apply_6(v_msg_2596_, v_fst_2603_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, lean_box(0));
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v___y_2624_ = v_ref_2635_;
v_a_2625_ = v_a_2637_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2638_; 
lean_dec_ref_known(v___x_2636_, 1);
v___x_2638_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1);
v___y_2624_ = v_ref_2635_;
v_a_2625_ = v___x_2638_;
goto v___jp_2623_;
}
}
v___jp_2639_:
{
if (v_clsEnabled_2594_ == 0)
{
if (v___y_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v_traceState_2642_; lean_object* v_env_2643_; lean_object* v_nextMacroScope_2644_; lean_object* v_ngen_2645_; lean_object* v_auxDeclNGen_2646_; lean_object* v_cache_2647_; lean_object* v_messages_2648_; lean_object* v_infoState_2649_; lean_object* v_snapshotTasks_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_snd_2620_);
lean_dec(v_fst_2619_);
lean_dec_ref(v_msg_2596_);
lean_dec_ref(v_tag_2592_);
lean_dec(v_cls_2590_);
v___x_2641_ = lean_st_ref_take(v___y_2601_);
v_traceState_2642_ = lean_ctor_get(v___x_2641_, 4);
v_env_2643_ = lean_ctor_get(v___x_2641_, 0);
v_nextMacroScope_2644_ = lean_ctor_get(v___x_2641_, 1);
v_ngen_2645_ = lean_ctor_get(v___x_2641_, 2);
v_auxDeclNGen_2646_ = lean_ctor_get(v___x_2641_, 3);
v_cache_2647_ = lean_ctor_get(v___x_2641_, 5);
v_messages_2648_ = lean_ctor_get(v___x_2641_, 6);
v_infoState_2649_ = lean_ctor_get(v___x_2641_, 7);
v_snapshotTasks_2650_ = lean_ctor_get(v___x_2641_, 8);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2652_ = v___x_2641_;
v_isShared_2653_ = v_isSharedCheck_2669_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_snapshotTasks_2650_);
lean_inc(v_infoState_2649_);
lean_inc(v_messages_2648_);
lean_inc(v_cache_2647_);
lean_inc(v_traceState_2642_);
lean_inc(v_auxDeclNGen_2646_);
lean_inc(v_ngen_2645_);
lean_inc(v_nextMacroScope_2644_);
lean_inc(v_env_2643_);
lean_dec(v___x_2641_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2669_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
uint64_t v_tid_2654_; lean_object* v_traces_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2668_; 
v_tid_2654_ = lean_ctor_get_uint64(v_traceState_2642_, sizeof(void*)*1);
v_traces_2655_ = lean_ctor_get(v_traceState_2642_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_traceState_2642_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2657_ = v_traceState_2642_;
v_isShared_2658_ = v_isSharedCheck_2668_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_traces_2655_);
lean_dec(v_traceState_2642_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2668_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2595_, v_traces_2655_);
lean_dec_ref(v_traces_2655_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2659_);
v___x_2661_ = v___x_2657_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2659_);
lean_ctor_set_uint64(v_reuseFailAlloc_2667_, sizeof(void*)*1, v_tid_2654_);
v___x_2661_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2663_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 4, v___x_2661_);
v___x_2663_ = v___x_2652_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_env_2643_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_nextMacroScope_2644_);
lean_ctor_set(v_reuseFailAlloc_2666_, 2, v_ngen_2645_);
lean_ctor_set(v_reuseFailAlloc_2666_, 3, v_auxDeclNGen_2646_);
lean_ctor_set(v_reuseFailAlloc_2666_, 4, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2666_, 5, v_cache_2647_);
lean_ctor_set(v_reuseFailAlloc_2666_, 6, v_messages_2648_);
lean_ctor_set(v_reuseFailAlloc_2666_, 7, v_infoState_2649_);
lean_ctor_set(v_reuseFailAlloc_2666_, 8, v_snapshotTasks_2650_);
v___x_2663_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_st_ref_put(v___y_2601_, v___x_2663_);
v___x_2665_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_fst_2603_);
return v___x_2665_;
}
}
}
}
}
else
{
goto v___jp_2634_;
}
}
else
{
goto v___jp_2634_;
}
}
v___jp_2670_:
{
double v___x_2672_; double v___x_2673_; double v___x_2674_; uint8_t v___x_2675_; 
v___x_2672_ = lean_unbox_float(v_snd_2620_);
v___x_2673_ = lean_unbox_float(v_fst_2619_);
v___x_2674_ = lean_float_sub(v___x_2672_, v___x_2673_);
v___x_2675_ = lean_float_decLt(v___y_2671_, v___x_2674_);
v___y_2640_ = v___x_2675_;
goto v___jp_2639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object* v_cls_2686_, lean_object* v_collapsed_2687_, lean_object* v_tag_2688_, lean_object* v_opts_2689_, lean_object* v_clsEnabled_2690_, lean_object* v_oldTraces_2691_, lean_object* v_msg_2692_, lean_object* v_resStartStop_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
uint8_t v_collapsed_boxed_2699_; uint8_t v_clsEnabled_boxed_2700_; lean_object* v_res_2701_; 
v_collapsed_boxed_2699_ = lean_unbox(v_collapsed_2687_);
v_clsEnabled_boxed_2700_ = lean_unbox(v_clsEnabled_2690_);
v_res_2701_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2686_, v_collapsed_boxed_2699_, v_tag_2688_, v_opts_2689_, v_clsEnabled_boxed_2700_, v_oldTraces_2691_, v_msg_2692_, v_resStartStop_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec_ref(v_opts_2689_);
return v_res_2701_;
}
}
static double _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0(void){
_start:
{
lean_object* v___x_2702_; double v___x_2703_; 
v___x_2702_ = lean_unsigned_to_nat(1000000000u);
v___x_2703_ = lean_float_of_nat(v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object* v_t_2704_, lean_object* v_s_2705_, lean_object* v_candidate_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_toCold_2712_; lean_object* v_options_2713_; lean_object* v_inheritedTraceOptions_2714_; uint8_t v_hasTrace_2715_; uint8_t v___x_2716_; 
v_toCold_2712_ = lean_ctor_get(v_a_2709_, 0);
v_options_2713_ = lean_ctor_get(v_toCold_2712_, 2);
v_inheritedTraceOptions_2714_ = lean_ctor_get(v_toCold_2712_, 11);
v_hasTrace_2715_ = lean_ctor_get_uint8(v_options_2713_, sizeof(void*)*1);
v___x_2716_ = 1;
if (v_hasTrace_2715_ == 0)
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2706_, v_t_2704_, v_s_2705_, v___x_2716_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2717_;
}
else
{
lean_object* v___f_2718_; lean_object* v_cls_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v_a_2726_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v_a_2741_; 
lean_inc_ref(v_s_2705_);
lean_inc_ref(v_t_2704_);
lean_inc(v_candidate_2706_);
v___f_2718_ = lean_alloc_closure((void*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2718_, 0, v_candidate_2706_);
lean_closure_set(v___f_2718_, 1, v_t_2704_);
lean_closure_set(v___f_2718_, 2, v_s_2705_);
v_cls_2719_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2720_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_2721_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2722_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2714_, v_options_2713_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2791_ = l_Lean_trace_profiler;
v___x_2792_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2713_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; 
lean_dec_ref(v___f_2718_);
v___x_2793_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2706_, v_t_2704_, v_s_2705_, v___x_2716_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2793_;
}
else
{
goto v___jp_2750_;
}
}
else
{
goto v___jp_2750_;
}
v___jp_2723_:
{
lean_object* v___x_2727_; double v___x_2728_; double v___x_2729_; double v___x_2730_; double v___x_2731_; double v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2727_ = lean_io_mono_nanos_now();
v___x_2728_ = lean_float_of_nat(v___y_2725_);
v___x_2729_ = lean_float_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0);
v___x_2730_ = lean_float_div(v___x_2728_, v___x_2729_);
v___x_2731_ = lean_float_of_nat(v___x_2727_);
v___x_2732_ = lean_float_div(v___x_2731_, v___x_2729_);
v___x_2733_ = lean_box_float(v___x_2730_);
v___x_2734_ = lean_box_float(v___x_2732_);
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_a_2726_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2719_, v___x_2716_, v___x_2720_, v_options_2713_, v___x_2722_, v___y_2724_, v___f_2718_, v___x_2736_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2737_;
}
v___jp_2738_:
{
lean_object* v___x_2742_; double v___x_2743_; double v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2742_ = lean_io_get_num_heartbeats();
v___x_2743_ = lean_float_of_nat(v___y_2739_);
v___x_2744_ = lean_float_of_nat(v___x_2742_);
v___x_2745_ = lean_box_float(v___x_2743_);
v___x_2746_ = lean_box_float(v___x_2744_);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v_a_2741_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2719_, v___x_2716_, v___x_2720_, v_options_2713_, v___x_2722_, v___y_2740_, v___f_2718_, v___x_2748_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2749_;
}
v___jp_2750_:
{
lean_object* v___x_2751_; lean_object* v_a_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2751_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v_a_2710_);
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref(v___x_2751_);
v___x_2753_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2754_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2713_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_io_mono_nanos_now();
v___x_2756_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2706_, v_t_2704_, v_s_2705_, v___x_2716_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 1);
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
v___y_2724_ = v_a_2752_;
v___y_2725_ = v___x_2755_;
v_a_2726_ = v___x_2762_;
goto v___jp_2723_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2756_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2756_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 0);
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
v___y_2724_ = v_a_2752_;
v___y_2725_ = v___x_2755_;
v_a_2726_ = v___x_2770_;
goto v___jp_2723_;
}
}
}
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = lean_io_get_num_heartbeats();
v___x_2774_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2706_, v_t_2704_, v_s_2705_, v___x_2716_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set_tag(v___x_2777_, 1);
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
v___y_2739_ = v___x_2773_;
v___y_2740_ = v_a_2752_;
v_a_2741_ = v___x_2780_;
goto v___jp_2738_;
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v_a_2783_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2774_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2774_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set_tag(v___x_2785_, 0);
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
v___y_2739_ = v___x_2773_;
v___y_2740_ = v_a_2752_;
v_a_2741_ = v___x_2788_;
goto v___jp_2738_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object* v_t_2794_, lean_object* v_s_2795_, lean_object* v_candidate_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2794_, v_s_2795_, v_candidate_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object* v_as_2803_, lean_object* v_as_x27_2804_, lean_object* v_b_2805_, lean_object* v_a_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2804_, v_b_2805_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object* v_as_2813_, lean_object* v_as_x27_2814_, lean_object* v_b_2815_, lean_object* v_a_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(v_as_2813_, v_as_x27_2814_, v_b_2815_, v_a_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v_as_x27_2814_);
lean_dec(v_as_2813_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(lean_object* v_00_u03b1_2823_, lean_object* v_x_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_x_2824_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2831_, lean_object* v_x_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_00_u03b1_2831_, v_x_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(lean_object* v_t_2839_, lean_object* v_s_2840_, uint8_t v___x_2841_, lean_object* v_as_2842_, size_t v_sz_2843_, size_t v_i_2844_, lean_object* v_b_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
uint8_t v___x_2851_; 
v___x_2851_ = lean_usize_dec_lt(v_i_2844_, v_sz_2843_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
lean_dec_ref(v_s_2840_);
lean_dec_ref(v_t_2839_);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_b_2845_);
return v___x_2852_;
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
lean_dec_ref(v_b_2845_);
v_a_2853_ = lean_array_uget_borrowed(v_as_2842_, v_i_2844_);
lean_inc(v_a_2853_);
lean_inc_ref(v_s_2840_);
lean_inc_ref(v_t_2839_);
v___x_2854_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2839_, v_s_2840_, v_a_2853_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2871_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2871_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2871_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = lean_box(0);
v___x_2860_ = lean_unbox(v_a_2855_);
lean_dec(v_a_2855_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; size_t v___x_2862_; size_t v___x_2863_; 
lean_del_object(v___x_2857_);
v___x_2861_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v___x_2862_ = ((size_t)1ULL);
v___x_2863_ = lean_usize_add(v_i_2844_, v___x_2862_);
v_i_2844_ = v___x_2863_;
v_b_2845_ = v___x_2861_;
goto _start;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
lean_dec_ref(v_s_2840_);
lean_dec_ref(v_t_2839_);
v___x_2865_ = lean_box(v___x_2841_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
lean_ctor_set(v___x_2867_, 1, v___x_2859_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2867_);
v___x_2869_ = v___x_2857_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec_ref(v_s_2840_);
lean_dec_ref(v_t_2839_);
v_a_2872_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2854_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2854_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object* v_t_2880_, lean_object* v_s_2881_, lean_object* v___x_2882_, lean_object* v_as_2883_, lean_object* v_sz_2884_, lean_object* v_i_2885_, lean_object* v_b_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v___x_2954__boxed_2892_; size_t v_sz_boxed_2893_; size_t v_i_boxed_2894_; lean_object* v_res_2895_; 
v___x_2954__boxed_2892_ = lean_unbox(v___x_2882_);
v_sz_boxed_2893_ = lean_unbox_usize(v_sz_2884_);
lean_dec(v_sz_2884_);
v_i_boxed_2894_ = lean_unbox_usize(v_i_2885_);
lean_dec(v_i_2885_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2880_, v_s_2881_, v___x_2954__boxed_2892_, v_as_2883_, v_sz_boxed_2893_, v_i_boxed_2894_, v_b_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v_as_2883_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* v_t_2896_, lean_object* v_s_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_toCold_2903_; lean_object* v_options_2904_; lean_object* v_inheritedTraceOptions_2905_; uint8_t v_hasTrace_2906_; lean_object* v___x_2907_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; 
v_toCold_2903_ = lean_ctor_get(v_a_2900_, 0);
v_options_2904_ = lean_ctor_get(v_toCold_2903_, 2);
v_inheritedTraceOptions_2905_ = lean_ctor_get(v_toCold_2903_, 11);
v_hasTrace_2906_ = lean_ctor_get_uint8(v_options_2904_, sizeof(void*)*1);
v___x_2907_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
if (v_hasTrace_2906_ == 0)
{
v___y_2909_ = v_a_2898_;
v___y_2910_ = v_a_2899_;
v___y_2911_ = v_a_2900_;
v___y_2912_ = v_a_2901_;
goto v___jp_2908_;
}
else
{
lean_object* v_cls_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_cls_2979_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2980_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2981_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2905_, v_options_2904_, v___x_2980_);
if (v___x_2981_ == 0)
{
v___y_2909_ = v_a_2898_;
v___y_2910_ = v_a_2899_;
v___y_2911_ = v_a_2900_;
v___y_2912_ = v_a_2901_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_inc_ref(v_t_2896_);
v___x_2982_ = l_Lean_MessageData_ofExpr(v_t_2896_);
v___x_2983_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
lean_inc_ref(v_s_2897_);
v___x_2985_ = l_Lean_MessageData_ofExpr(v_s_2897_);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2979_, v___x_2986_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_dec_ref_known(v___x_2987_, 1);
v___y_2909_ = v_a_2898_;
v___y_2910_ = v_a_2899_;
v___y_2911_ = v_a_2900_;
v___y_2912_ = v_a_2901_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v_s_2897_);
lean_dec_ref(v_t_2896_);
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
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
}
v___jp_2908_:
{
lean_object* v___x_2913_; uint8_t v_unificationHints_2914_; 
v___x_2913_ = l_Lean_Meta_Context_config(v___y_2909_);
v_unificationHints_2914_ = lean_ctor_get_uint8(v___x_2913_, 5);
lean_dec_ref(v___x_2913_);
if (v_unificationHints_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
lean_dec_ref(v_s_2897_);
lean_dec_ref(v_t_2896_);
v___x_2915_ = lean_box(v_unificationHints_2914_);
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
return v___x_2916_;
}
else
{
uint8_t v___x_2917_; 
v___x_2917_ = l_Lean_Expr_isMVar(v_t_2896_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v_env_2919_; lean_object* v___x_2920_; lean_object* v_ext_2921_; lean_object* v_toEnvExtension_2922_; lean_object* v_asyncMode_2923_; lean_object* v___x_2924_; lean_object* v_config_2925_; uint8_t v_trackZetaDelta_2926_; lean_object* v_zetaDeltaSet_2927_; lean_object* v_lctx_2928_; lean_object* v_localInstances_2929_; lean_object* v_defEqCtx_x3f_2930_; lean_object* v_synthPendingDepth_2931_; lean_object* v_customCanUnfoldPredicate_x3f_2932_; uint8_t v_univApprox_2933_; uint8_t v_inTypeClassResolution_2934_; uint8_t v_cacheInferType_2935_; uint64_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2918_ = lean_st_ref_get(v___y_2912_);
v_env_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc_ref(v_env_2919_);
lean_dec(v___x_2918_);
v___x_2920_ = l_Lean_Meta_unificationHintExtension;
v_ext_2921_ = lean_ctor_get(v___x_2920_, 1);
v_toEnvExtension_2922_ = lean_ctor_get(v_ext_2921_, 0);
v_asyncMode_2923_ = lean_ctor_get(v_toEnvExtension_2922_, 2);
v___x_2924_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_2925_ = lean_ctor_get(v___x_2924_, 0);
v_trackZetaDelta_2926_ = lean_ctor_get_uint8(v___y_2909_, sizeof(void*)*7);
v_zetaDeltaSet_2927_ = lean_ctor_get(v___y_2909_, 1);
v_lctx_2928_ = lean_ctor_get(v___y_2909_, 2);
v_localInstances_2929_ = lean_ctor_get(v___y_2909_, 3);
v_defEqCtx_x3f_2930_ = lean_ctor_get(v___y_2909_, 4);
v_synthPendingDepth_2931_ = lean_ctor_get(v___y_2909_, 5);
v_customCanUnfoldPredicate_x3f_2932_ = lean_ctor_get(v___y_2909_, 6);
v_univApprox_2933_ = lean_ctor_get_uint8(v___y_2909_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2934_ = lean_ctor_get_uint8(v___y_2909_, sizeof(void*)*7 + 2);
v_cacheInferType_2935_ = lean_ctor_get_uint8(v___y_2909_, sizeof(void*)*7 + 3);
v___x_2936_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2925_);
v___x_2937_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2907_, v___x_2920_, v_env_2919_, v_asyncMode_2923_);
lean_inc_ref(v_config_2925_);
v___x_2938_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2938_, 0, v_config_2925_);
lean_ctor_set_uint64(v___x_2938_, sizeof(void*)*1, v___x_2936_);
lean_inc(v_customCanUnfoldPredicate_x3f_2932_);
lean_inc(v_synthPendingDepth_2931_);
lean_inc(v_defEqCtx_x3f_2930_);
lean_inc_ref(v_localInstances_2929_);
lean_inc_ref(v_lctx_2928_);
lean_inc(v_zetaDeltaSet_2927_);
v___x_2939_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v_zetaDeltaSet_2927_);
lean_ctor_set(v___x_2939_, 2, v_lctx_2928_);
lean_ctor_set(v___x_2939_, 3, v_localInstances_2929_);
lean_ctor_set(v___x_2939_, 4, v_defEqCtx_x3f_2930_);
lean_ctor_set(v___x_2939_, 5, v_synthPendingDepth_2931_);
lean_ctor_set(v___x_2939_, 6, v_customCanUnfoldPredicate_x3f_2932_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*7, v_trackZetaDelta_2926_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*7 + 1, v_univApprox_2933_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2934_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*7 + 3, v_cacheInferType_2935_);
lean_inc_ref(v_t_2896_);
v___x_2940_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v___x_2937_, v_t_2896_, v___x_2939_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec_ref_known(v___x_2939_, 7);
lean_dec(v___x_2937_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; size_t v_sz_2943_; size_t v___x_2944_; lean_object* v___x_2945_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_sz_2943_ = lean_array_size(v_a_2941_);
v___x_2944_ = ((size_t)0ULL);
v___x_2945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2896_, v_s_2897_, v_unificationHints_2914_, v_a_2941_, v_sz_2943_, v___x_2944_, v___x_2942_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec(v_a_2941_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2959_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2959_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2959_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v_fst_2950_; 
v_fst_2950_ = lean_ctor_get(v_a_2946_, 0);
lean_inc(v_fst_2950_);
lean_dec(v_a_2946_);
if (lean_obj_tag(v_fst_2950_) == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2951_ = lean_box(v___x_2917_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2951_);
v___x_2953_ = v___x_2948_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
else
{
lean_object* v_val_2955_; lean_object* v___x_2957_; 
v_val_2955_ = lean_ctor_get(v_fst_2950_, 0);
lean_inc(v_val_2955_);
lean_dec_ref_known(v_fst_2950_, 1);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v_val_2955_);
v___x_2957_ = v___x_2948_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_val_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
v_a_2960_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2945_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2945_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec_ref(v_s_2897_);
lean_dec_ref(v_t_2896_);
v_a_2968_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2940_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2940_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
uint8_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec_ref(v_s_2897_);
lean_dec_ref(v_t_2896_);
v___x_2976_ = 0;
v___x_2977_ = lean_box(v___x_2976_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___boxed(lean_object* v_t_2996_, lean_object* v_s_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_Meta_tryUnificationHints(v_t_2996_, v_s_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_);
lean_dec(v_a_3001_);
lean_dec_ref(v_a_3000_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
return v_res_3003_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = lean_unsigned_to_nat(2674080740u);
v___x_3005_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3006_ = l_Lean_Name_num___override(v___x_3005_, v___x_3004_);
return v___x_3006_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3007_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3008_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3009_ = l_Lean_Name_str___override(v___x_3008_, v___x_3007_);
return v___x_3009_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3011_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3012_ = l_Lean_Name_str___override(v___x_3011_, v___x_3010_);
return v___x_3012_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_unsigned_to_nat(2u);
v___x_3014_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3015_ = l_Lean_Name_num___override(v___x_3014_, v___x_3013_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3017_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_3018_ = 0;
v___x_3019_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3020_ = l_Lean_registerTraceClass(v___x_3017_, v___x_3018_, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
return v_res_3022_;
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
