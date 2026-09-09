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
lean_object* v___x_738_; lean_object* v_env_739_; lean_object* v___x_740_; lean_object* v_mctx_741_; lean_object* v_lctx_742_; lean_object* v_options_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_738_ = lean_st_ref_get(v___y_736_);
v_env_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_env_739_);
lean_dec(v___x_738_);
v___x_740_ = lean_st_ref_get(v___y_734_);
v_mctx_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc_ref(v_mctx_741_);
lean_dec(v___x_740_);
v_lctx_742_ = lean_ctor_get(v___y_733_, 2);
v_options_743_ = lean_ctor_get(v___y_735_, 1);
lean_inc_ref(v_options_743_);
lean_inc_ref(v_lctx_742_);
v___x_744_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_744_, 0, v_env_739_);
lean_ctor_set(v___x_744_, 1, v_mctx_741_);
lean_ctor_set(v___x_744_, 2, v_lctx_742_);
lean_ctor_set(v___x_744_, 3, v_options_743_);
v___x_745_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v_msgData_732_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object* v_msgData_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msgData_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(lean_object* v_msg_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_ref_760_; lean_object* v___x_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_770_; 
v_ref_760_ = lean_ctor_get(v___y_757_, 4);
v___x_761_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_770_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_inc(v_ref_760_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_ref_760_);
lean_ctor_set(v___x_766_, 1, v_a_762_);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 1);
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg___boxed(lean_object* v_msg_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_777_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0));
v___x_780_ = l_Lean_stringToMessageData(v___x_779_);
return v___x_780_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2));
v___x_783_ = l_Lean_stringToMessageData(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(lean_object* v_as_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
if (lean_obj_tag(v_as_784_) == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_box(0);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
else
{
lean_object* v_head_792_; lean_object* v_tail_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_827_; 
v_head_792_ = lean_ctor_get(v_as_784_, 0);
v_tail_793_ = lean_ctor_get(v_as_784_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_as_784_);
if (v_isSharedCheck_827_ == 0)
{
v___x_795_ = v_as_784_;
v_isShared_796_ = v_isSharedCheck_827_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_tail_793_);
lean_inc(v_head_792_);
lean_dec(v_as_784_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_827_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_lhs_797_; lean_object* v_rhs_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_826_; 
v_lhs_797_ = lean_ctor_get(v_head_792_, 0);
v_rhs_798_ = lean_ctor_get(v_head_792_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_head_792_);
if (v_isSharedCheck_826_ == 0)
{
v___x_800_ = v_head_792_;
v_isShared_801_ = v_isSharedCheck_826_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_rhs_798_);
lean_inc(v_lhs_797_);
lean_dec(v_head_792_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_826_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; 
lean_inc_ref(v_rhs_798_);
lean_inc_ref(v_lhs_797_);
v___x_802_ = l_Lean_Meta_isExprDefEq(v_lhs_797_, v_rhs_798_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; uint8_t v___x_804_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = lean_unbox(v_a_803_);
lean_dec(v_a_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v_tail_793_);
v___x_805_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1);
v___x_806_ = l_Lean_indentExpr(v_lhs_797_);
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 7);
lean_ctor_set(v___x_800_, 1, v___x_806_);
lean_ctor_set(v___x_800_, 0, v___x_805_);
v___x_808_ = v___x_800_;
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
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 7);
lean_ctor_set(v___x_795_, 1, v___x_809_);
lean_ctor_set(v___x_795_, 0, v___x_808_);
v___x_811_ = v___x_795_;
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
v___x_812_ = l_Lean_indentExpr(v_rhs_798_);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_813_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v___x_814_;
}
}
}
else
{
lean_del_object(v___x_800_);
lean_dec_ref(v_rhs_798_);
lean_dec_ref(v_lhs_797_);
lean_del_object(v___x_795_);
v_as_784_ = v_tail_793_;
goto _start;
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_del_object(v___x_800_);
lean_dec_ref(v_rhs_798_);
lean_dec_ref(v_lhs_797_);
lean_del_object(v___x_795_);
lean_dec(v_tail_793_);
v_a_818_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_802_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_802_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___boxed(lean_object* v_as_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_as_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
return v_res_834_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0));
v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object* v_hint_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_pattern_844_; lean_object* v_constraints_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_887_; 
v_pattern_844_ = lean_ctor_get(v_hint_838_, 0);
v_constraints_845_ = lean_ctor_get(v_hint_838_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_hint_838_);
if (v_isSharedCheck_887_ == 0)
{
v___x_847_ = v_hint_838_;
v_isShared_848_ = v_isSharedCheck_887_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_constraints_845_);
lean_inc(v_pattern_844_);
lean_dec(v_hint_838_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_887_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; 
v___x_849_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_constraints_845_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_lhs_850_; lean_object* v_rhs_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref_known(v___x_849_, 1);
v_lhs_850_ = lean_ctor_get(v_pattern_844_, 0);
v_rhs_851_ = lean_ctor_get(v_pattern_844_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_pattern_844_);
if (v_isSharedCheck_886_ == 0)
{
v___x_853_ = v_pattern_844_;
v_isShared_854_ = v_isSharedCheck_886_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_rhs_851_);
lean_inc(v_lhs_850_);
lean_dec(v_pattern_844_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_886_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; 
lean_inc_ref(v_rhs_851_);
lean_inc_ref(v_lhs_850_);
v___x_855_ = l_Lean_Meta_isExprDefEq(v_lhs_850_, v_rhs_851_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_877_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_877_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_877_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_877_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
uint8_t v___x_860_; 
v___x_860_ = lean_unbox(v_a_856_);
lean_dec(v_a_856_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
lean_del_object(v___x_858_);
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1);
v___x_862_ = l_Lean_indentExpr(v_lhs_850_);
if (v_isShared_854_ == 0)
{
lean_ctor_set_tag(v___x_853_, 7);
lean_ctor_set(v___x_853_, 1, v___x_862_);
lean_ctor_set(v___x_853_, 0, v___x_861_);
v___x_864_ = v___x_853_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_862_);
v___x_864_ = v_reuseFailAlloc_872_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3, &l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once, _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 7);
lean_ctor_set(v___x_847_, 1, v___x_865_);
lean_ctor_set(v___x_847_, 0, v___x_864_);
v___x_867_ = v___x_847_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_865_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = l_Lean_indentExpr(v_rhs_851_);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_869_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
return v___x_870_;
}
}
}
else
{
lean_object* v___x_873_; lean_object* v___x_875_; 
lean_del_object(v___x_853_);
lean_dec_ref(v_rhs_851_);
lean_dec_ref(v_lhs_850_);
lean_del_object(v___x_847_);
v___x_873_ = lean_box(0);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_873_);
v___x_875_ = v___x_858_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_del_object(v___x_853_);
lean_dec_ref(v_rhs_851_);
lean_dec_ref(v_lhs_850_);
lean_del_object(v___x_847_);
v_a_878_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_855_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_855_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
else
{
lean_del_object(v___x_847_);
lean_dec_ref(v_pattern_844_);
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object* v_hint_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_hint_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object* v_00_u03b1_895_, lean_object* v_msg_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object* v_00_u03b1_903_, lean_object* v_msg_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(v_00_u03b1_903_, v_msg_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_910_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_911_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
v___x_917_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
lean_ctor_set(v___x_917_, 2, v___x_916_);
lean_ctor_set(v___x_917_, 3, v___x_916_);
lean_ctor_set(v___x_917_, 4, v___x_916_);
lean_ctor_set(v___x_917_, 5, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(lean_object* v_ext_918_, lean_object* v_b_919_, uint8_t v_kind_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_currNamespace_925_; lean_object* v___x_926_; lean_object* v_env_927_; lean_object* v_nextMacroScope_928_; lean_object* v_ngen_929_; lean_object* v_auxDeclNGen_930_; lean_object* v_traceState_931_; lean_object* v_messages_932_; lean_object* v_infoState_933_; lean_object* v_snapshotTasks_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_961_; 
v_currNamespace_925_ = lean_ctor_get(v___y_922_, 5);
v___x_926_ = lean_st_ref_take(v___y_923_);
v_env_927_ = lean_ctor_get(v___x_926_, 0);
v_nextMacroScope_928_ = lean_ctor_get(v___x_926_, 1);
v_ngen_929_ = lean_ctor_get(v___x_926_, 2);
v_auxDeclNGen_930_ = lean_ctor_get(v___x_926_, 3);
v_traceState_931_ = lean_ctor_get(v___x_926_, 4);
v_messages_932_ = lean_ctor_get(v___x_926_, 6);
v_infoState_933_ = lean_ctor_get(v___x_926_, 7);
v_snapshotTasks_934_ = lean_ctor_get(v___x_926_, 8);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v___x_926_, 5);
lean_dec(v_unused_962_);
v___x_936_ = v___x_926_;
v_isShared_937_ = v_isSharedCheck_961_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_snapshotTasks_934_);
lean_inc(v_infoState_933_);
lean_inc(v_messages_932_);
lean_inc(v_traceState_931_);
lean_inc(v_auxDeclNGen_930_);
lean_inc(v_ngen_929_);
lean_inc(v_nextMacroScope_928_);
lean_inc(v_env_927_);
lean_dec(v___x_926_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_961_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
lean_inc(v_currNamespace_925_);
v___x_938_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_927_, v_ext_918_, v_b_919_, v_kind_920_, v_currNamespace_925_);
v___x_939_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 5, v___x_939_);
lean_ctor_set(v___x_936_, 0, v___x_938_);
v___x_941_ = v___x_936_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_nextMacroScope_928_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_ngen_929_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_auxDeclNGen_930_);
lean_ctor_set(v_reuseFailAlloc_960_, 4, v_traceState_931_);
lean_ctor_set(v_reuseFailAlloc_960_, 5, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_960_, 6, v_messages_932_);
lean_ctor_set(v_reuseFailAlloc_960_, 7, v_infoState_933_);
lean_ctor_set(v_reuseFailAlloc_960_, 8, v_snapshotTasks_934_);
v___x_941_ = v_reuseFailAlloc_960_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_mctx_944_; lean_object* v_zetaDeltaFVarIds_945_; lean_object* v_postponed_946_; lean_object* v_diag_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_958_; 
v___x_942_ = lean_st_ref_put(v___y_923_, v___x_941_);
v___x_943_ = lean_st_ref_take(v___y_921_);
v_mctx_944_ = lean_ctor_get(v___x_943_, 0);
v_zetaDeltaFVarIds_945_ = lean_ctor_get(v___x_943_, 2);
v_postponed_946_ = lean_ctor_get(v___x_943_, 3);
v_diag_947_ = lean_ctor_get(v___x_943_, 4);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v___x_943_, 1);
lean_dec(v_unused_959_);
v___x_949_ = v___x_943_;
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_diag_947_);
lean_inc(v_postponed_946_);
lean_inc(v_zetaDeltaFVarIds_945_);
lean_inc(v_mctx_944_);
lean_dec(v___x_943_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_mctx_944_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_zetaDeltaFVarIds_945_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_postponed_946_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_diag_947_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_st_ref_put(v___y_921_, v___x_953_);
v___x_955_ = lean_box(0);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(lean_object* v_ext_963_, lean_object* v_b_964_, lean_object* v_kind_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
uint8_t v_kind_boxed_970_; lean_object* v_res_971_; 
v_kind_boxed_970_ = lean_unbox(v_kind_965_);
v_res_971_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_963_, v_b_964_, v_kind_boxed_970_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_00_u03c3_974_, lean_object* v_ext_975_, lean_object* v_b_976_, uint8_t v_kind_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v_ext_975_, v_b_976_, v_kind_977_, v___y_979_, v___y_980_, v___y_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(lean_object* v_00_u03b1_984_, lean_object* v_00_u03b2_985_, lean_object* v_00_u03c3_986_, lean_object* v_ext_987_, lean_object* v_b_988_, lean_object* v_kind_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_kind_boxed_995_; lean_object* v_res_996_; 
v_kind_boxed_995_ = lean_unbox(v_kind_989_);
v_res_996_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(v_00_u03b1_984_, v_00_u03b2_985_, v_00_u03c3_986_, v_ext_987_, v_b_988_, v_kind_boxed_995_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(lean_object* v_k_997_, uint8_t v_allowLevelAssignments_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_998_, v_k_997_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1004_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1004_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(lean_object* v_k_1021_, lean_object* v_allowLevelAssignments_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1028_; lean_object* v_res_1029_; 
v_allowLevelAssignments_boxed_1028_ = lean_unbox(v_allowLevelAssignments_1022_);
v_res_1029_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_1021_, v_allowLevelAssignments_boxed_1028_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(lean_object* v_00_u03b1_1030_, lean_object* v_k_1031_, uint8_t v_allowLevelAssignments_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v_k_1031_, v_allowLevelAssignments_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_k_1040_, lean_object* v_allowLevelAssignments_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1047_; lean_object* v_res_1048_; 
v_allowLevelAssignments_boxed_1047_ = lean_unbox(v_allowLevelAssignments_1041_);
v_res_1048_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(v_00_u03b1_1039_, v_k_1040_, v_allowLevelAssignments_boxed_1047_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1048_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
lean_ctor_set(v___x_1054_, 2, v___x_1053_);
lean_ctor_set(v___x_1054_, 3, v___x_1053_);
lean_ctor_set(v___x_1054_, 4, v___x_1052_);
lean_ctor_set(v___x_1054_, 5, v___x_1052_);
lean_ctor_set(v___x_1054_, 6, v___x_1052_);
lean_ctor_set(v___x_1054_, 7, v___x_1052_);
lean_ctor_set(v___x_1054_, 8, v___x_1052_);
lean_ctor_set(v___x_1054_, 9, v___x_1052_);
lean_ctor_set(v___x_1054_, 10, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1055_ = lean_unsigned_to_nat(32u);
v___x_1056_ = lean_mk_empty_array_with_capacity(v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1058_ = ((size_t)5ULL);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_unsigned_to_nat(32u);
v___x_1061_ = lean_mk_empty_array_with_capacity(v___x_1060_);
v___x_1062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1063_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___x_1061_);
lean_ctor_set(v___x_1063_, 2, v___x_1059_);
lean_ctor_set(v___x_1063_, 3, v___x_1059_);
lean_ctor_set_usize(v___x_1063_, 4, v___x_1058_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = lean_box(1);
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
lean_ctor_set(v___x_1067_, 2, v___x_1064_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1089_, lean_object* v_declHint_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v_env_1094_; uint8_t v___x_1095_; 
v___x_1093_ = lean_st_ref_get(v___y_1091_);
v_env_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_ref(v_env_1094_);
lean_dec(v___x_1093_);
v___x_1095_ = l_Lean_Name_isAnonymous(v_declHint_1090_);
if (v___x_1095_ == 0)
{
uint8_t v_isExporting_1096_; 
v_isExporting_1096_ = lean_ctor_get_uint8(v_env_1094_, sizeof(void*)*8);
if (v_isExporting_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec_ref(v_env_1094_);
lean_dec(v_declHint_1090_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_msg_1089_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
lean_inc_ref(v_env_1094_);
v___x_1098_ = l_Lean_Environment_setExporting(v_env_1094_, v___x_1095_);
lean_inc(v_declHint_1090_);
lean_inc_ref(v___x_1098_);
v___x_1099_ = l_Lean_Environment_contains(v___x_1098_, v_declHint_1090_, v_isExporting_1096_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref(v___x_1098_);
lean_dec_ref(v_env_1094_);
lean_dec(v_declHint_1090_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_msg_1089_);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_c_1106_; lean_object* v___x_1107_; 
v___x_1101_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1103_ = l_Lean_Options_empty;
v___x_1104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1098_);
lean_ctor_set(v___x_1104_, 1, v___x_1101_);
lean_ctor_set(v___x_1104_, 2, v___x_1102_);
lean_ctor_set(v___x_1104_, 3, v___x_1103_);
lean_inc(v_declHint_1090_);
v___x_1105_ = l_Lean_MessageData_ofConstName(v_declHint_1090_, v___x_1095_);
v_c_1106_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1106_, 0, v___x_1104_);
lean_ctor_set(v_c_1106_, 1, v___x_1105_);
v___x_1107_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1094_, v_declHint_1090_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v_env_1094_);
lean_dec(v_declHint_1090_);
v___x_1108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_c_1106_);
v___x_1110_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_MessageData_note(v___x_1111_);
v___x_1113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1113_, 0, v_msg_1089_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
else
{
lean_object* v_val_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1150_; 
v_val_1115_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1117_ = v___x_1107_;
v_isShared_1118_ = v_isSharedCheck_1150_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_val_1115_);
lean_dec(v___x_1107_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1150_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_mod_1122_; uint8_t v___x_1123_; 
v___x_1119_ = lean_box(0);
v___x_1120_ = l_Lean_Environment_header(v_env_1094_);
lean_dec_ref(v_env_1094_);
v___x_1121_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1120_);
v_mod_1122_ = lean_array_get(v___x_1119_, v___x_1121_, v_val_1115_);
lean_dec(v_val_1115_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = l_Lean_isPrivateName(v_declHint_1090_);
lean_dec(v_declHint_1090_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v_c_1106_);
v___x_1126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_MessageData_ofName(v_mod_1122_);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_MessageData_note(v___x_1131_);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_msg_1089_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1133_);
v___x_1135_ = v___x_1117_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v_c_1106_);
v___x_1139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_MessageData_ofName(v_mod_1122_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_MessageData_note(v___x_1144_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_msg_1089_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1146_);
v___x_1148_ = v___x_1117_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1151_; 
lean_dec_ref(v_env_1094_);
lean_dec(v_declHint_1090_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_msg_1089_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1152_, lean_object* v_declHint_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1152_, v_declHint_1153_, v___y_1154_);
lean_dec(v___y_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object* v_msg_1157_, lean_object* v_declHint_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1174_; 
v___x_1164_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1157_, v_declHint_1158_, v___y_1162_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1169_ = l_Lean_unknownIdentifierMessageTag;
v___x_1170_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v_a_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1175_, lean_object* v_declHint_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1175_, v_declHint_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1183_, lean_object* v_msg_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_toCold_1190_; lean_object* v_options_1191_; lean_object* v_currRecDepth_1192_; lean_object* v_maxRecDepth_1193_; lean_object* v_ref_1194_; lean_object* v_currNamespace_1195_; lean_object* v_openDecls_1196_; lean_object* v_initHeartbeats_1197_; lean_object* v_maxHeartbeats_1198_; lean_object* v_currMacroScope_1199_; uint8_t v_diag_1200_; uint8_t v_suppressElabErrors_1201_; lean_object* v_ref_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_toCold_1190_ = lean_ctor_get(v___y_1187_, 0);
v_options_1191_ = lean_ctor_get(v___y_1187_, 1);
v_currRecDepth_1192_ = lean_ctor_get(v___y_1187_, 2);
v_maxRecDepth_1193_ = lean_ctor_get(v___y_1187_, 3);
v_ref_1194_ = lean_ctor_get(v___y_1187_, 4);
v_currNamespace_1195_ = lean_ctor_get(v___y_1187_, 5);
v_openDecls_1196_ = lean_ctor_get(v___y_1187_, 6);
v_initHeartbeats_1197_ = lean_ctor_get(v___y_1187_, 7);
v_maxHeartbeats_1198_ = lean_ctor_get(v___y_1187_, 8);
v_currMacroScope_1199_ = lean_ctor_get(v___y_1187_, 9);
v_diag_1200_ = lean_ctor_get_uint8(v___y_1187_, sizeof(void*)*10);
v_suppressElabErrors_1201_ = lean_ctor_get_uint8(v___y_1187_, sizeof(void*)*10 + 1);
v_ref_1202_ = l_Lean_replaceRef(v_ref_1183_, v_ref_1194_);
lean_inc(v_currMacroScope_1199_);
lean_inc(v_maxHeartbeats_1198_);
lean_inc(v_initHeartbeats_1197_);
lean_inc(v_openDecls_1196_);
lean_inc(v_currNamespace_1195_);
lean_inc(v_maxRecDepth_1193_);
lean_inc(v_currRecDepth_1192_);
lean_inc_ref(v_options_1191_);
lean_inc_ref(v_toCold_1190_);
v___x_1203_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1203_, 0, v_toCold_1190_);
lean_ctor_set(v___x_1203_, 1, v_options_1191_);
lean_ctor_set(v___x_1203_, 2, v_currRecDepth_1192_);
lean_ctor_set(v___x_1203_, 3, v_maxRecDepth_1193_);
lean_ctor_set(v___x_1203_, 4, v_ref_1202_);
lean_ctor_set(v___x_1203_, 5, v_currNamespace_1195_);
lean_ctor_set(v___x_1203_, 6, v_openDecls_1196_);
lean_ctor_set(v___x_1203_, 7, v_initHeartbeats_1197_);
lean_ctor_set(v___x_1203_, 8, v_maxHeartbeats_1198_);
lean_ctor_set(v___x_1203_, 9, v_currMacroScope_1199_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*10, v_diag_1200_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*10 + 1, v_suppressElabErrors_1201_);
v___x_1204_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_1184_, v___y_1185_, v___y_1186_, v___x_1203_, v___y_1188_);
lean_dec_ref_known(v___x_1203_, 10);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1205_, lean_object* v_msg_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1205_, v_msg_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v_ref_1205_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_ref_1213_, lean_object* v_msg_1214_, lean_object* v_declHint_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v_a_1222_; lean_object* v___x_1223_; 
v___x_1221_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_1214_, v_declHint_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref(v___x_1221_);
v___x_1223_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1213_, v_a_1222_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1224_, lean_object* v_msg_1225_, lean_object* v_declHint_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1224_, v_msg_1225_, v_declHint_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v_ref_1224_);
return v_res_1232_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1235_ = l_Lean_stringToMessageData(v___x_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1238_ = l_Lean_stringToMessageData(v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1239_, lean_object* v_constName_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1246_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1247_ = 0;
lean_inc(v_constName_1240_);
v___x_1248_ = l_Lean_MessageData_ofConstName(v_constName_1240_, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1246_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1239_, v___x_1251_, v_constName_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1253_, lean_object* v_constName_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1253_, v_constName_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v_ref_1253_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(lean_object* v_constName_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_ref_1267_; lean_object* v___x_1268_; 
v_ref_1267_ = lean_ctor_get(v___y_1264_, 4);
v___x_1268_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1267_, v_constName_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(lean_object* v_constName_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; lean_object* v_env_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = lean_st_ref_get(v___y_1280_);
v_env_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_ref(v_env_1283_);
lean_dec(v___x_1282_);
v___x_1284_ = 0;
lean_inc(v_constName_1276_);
v___x_1285_ = l_Lean_Environment_find_x3f(v_env_1283_, v_constName_1276_, v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1286_;
}
else
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_constName_1276_);
v_val_1287_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1285_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v___x_1285_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 0);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_val_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(lean_object* v_constName_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_constName_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1301_;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Meta_addUnificationHint___lam__0___closed__0));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object* v_declName_1305_, uint8_t v_kind_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
lean_inc(v_declName_1305_);
v___x_1312_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_declName_1305_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = 0;
v___x_1315_ = l_Lean_ConstantInfo_value_x3f(v_a_1313_, v___x_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v_declName_1305_);
v___x_1316_ = lean_obj_once(&l_Lean_Meta_addUnificationHint___lam__0___closed__1, &l_Lean_Meta_addUnificationHint___lam__0___closed__1_once, _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1);
v___x_1317_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_1316_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1317_;
}
else
{
lean_object* v_val_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_val_1318_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1319_ = lean_box(0);
v___x_1320_ = l_Lean_Meta_lambdaMetaTelescope(v_val_1318_, v___x_1319_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v_val_1318_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v_snd_1322_; lean_object* v_snd_1323_; lean_object* v___x_1324_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v_snd_1322_ = lean_ctor_get(v_a_1321_, 1);
lean_inc(v_snd_1322_);
lean_dec(v_a_1321_);
v_snd_1323_ = lean_ctor_get(v_snd_1322_, 1);
lean_inc(v_snd_1323_);
lean_dec(v_snd_1322_);
v___x_1324_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_1323_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1326_; 
lean_dec(v_declName_1305_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v___x_1326_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_a_1325_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1326_;
}
else
{
lean_object* v_a_1327_; lean_object* v_pattern_1328_; lean_object* v_lhs_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1364_; 
v_a_1327_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1324_, 1);
v_pattern_1328_ = lean_ctor_get(v_a_1327_, 0);
lean_inc_ref(v_pattern_1328_);
v_lhs_1329_ = lean_ctor_get(v_pattern_1328_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_pattern_1328_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v_pattern_1328_, 1);
lean_dec(v_unused_1365_);
v___x_1331_ = v_pattern_1328_;
v_isShared_1332_ = v_isSharedCheck_1364_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_lhs_1329_);
lean_dec(v_pattern_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1364_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v_config_1334_; uint8_t v_trackZetaDelta_1335_; lean_object* v_zetaDeltaSet_1336_; lean_object* v_lctx_1337_; lean_object* v_localInstances_1338_; lean_object* v_defEqCtx_x3f_1339_; lean_object* v_synthPendingDepth_1340_; lean_object* v_customCanUnfoldPredicate_x3f_1341_; uint8_t v_univApprox_1342_; uint8_t v_inTypeClassResolution_1343_; uint8_t v_cacheInferType_1344_; uint64_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1333_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_1334_ = lean_ctor_get(v___x_1333_, 0);
v_trackZetaDelta_1335_ = lean_ctor_get_uint8(v___y_1307_, sizeof(void*)*7);
v_zetaDeltaSet_1336_ = lean_ctor_get(v___y_1307_, 1);
v_lctx_1337_ = lean_ctor_get(v___y_1307_, 2);
v_localInstances_1338_ = lean_ctor_get(v___y_1307_, 3);
v_defEqCtx_x3f_1339_ = lean_ctor_get(v___y_1307_, 4);
v_synthPendingDepth_1340_ = lean_ctor_get(v___y_1307_, 5);
v_customCanUnfoldPredicate_x3f_1341_ = lean_ctor_get(v___y_1307_, 6);
v_univApprox_1342_ = lean_ctor_get_uint8(v___y_1307_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1343_ = lean_ctor_get_uint8(v___y_1307_, sizeof(void*)*7 + 2);
v_cacheInferType_1344_ = lean_ctor_get_uint8(v___y_1307_, sizeof(void*)*7 + 3);
v___x_1345_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1334_);
lean_inc_ref(v_config_1334_);
v___x_1346_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1346_, 0, v_config_1334_);
lean_ctor_set_uint64(v___x_1346_, sizeof(void*)*1, v___x_1345_);
lean_inc(v_customCanUnfoldPredicate_x3f_1341_);
lean_inc(v_synthPendingDepth_1340_);
lean_inc(v_defEqCtx_x3f_1339_);
lean_inc_ref(v_localInstances_1338_);
lean_inc_ref(v_lctx_1337_);
lean_inc(v_zetaDeltaSet_1336_);
v___x_1347_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v_zetaDeltaSet_1336_);
lean_ctor_set(v___x_1347_, 2, v_lctx_1337_);
lean_ctor_set(v___x_1347_, 3, v_localInstances_1338_);
lean_ctor_set(v___x_1347_, 4, v_defEqCtx_x3f_1339_);
lean_ctor_set(v___x_1347_, 5, v_synthPendingDepth_1340_);
lean_ctor_set(v___x_1347_, 6, v_customCanUnfoldPredicate_x3f_1341_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*7, v_trackZetaDelta_1335_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*7 + 1, v_univApprox_1342_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1343_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*7 + 3, v_cacheInferType_1344_);
v___x_1348_ = l_Lean_Meta_DiscrTree_mkPath(v_lhs_1329_, v___x_1314_, v___x_1347_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec_ref_known(v___x_1347_, 7);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(v_a_1327_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec_ref_known(v___x_1350_, 1);
v___x_1351_ = l_Lean_Meta_unificationHintExtension;
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v_declName_1305_);
lean_ctor_set(v___x_1331_, 0, v_a_1349_);
v___x_1353_ = v___x_1331_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_declName_1305_);
v___x_1353_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v___x_1351_, v___x_1353_, v_kind_1306_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1354_;
}
}
else
{
lean_dec(v_a_1349_);
lean_del_object(v___x_1331_);
lean_dec(v_declName_1305_);
return v___x_1350_;
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_del_object(v___x_1331_);
lean_dec(v_a_1327_);
lean_dec(v_declName_1305_);
v_a_1356_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1348_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1348_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_declName_1305_);
v_a_1366_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1320_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1320_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_declName_1305_);
v_a_1374_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1312_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1312_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object* v_declName_1382_, lean_object* v_kind_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
uint8_t v_kind_boxed_1389_; lean_object* v_res_1390_; 
v_kind_boxed_1389_ = lean_unbox(v_kind_1383_);
v_res_1390_ = l_Lean_Meta_addUnificationHint___lam__0(v_declName_1382_, v_kind_boxed_1389_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* v_declName_1391_, uint8_t v_kind_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v___f_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = lean_box(v_kind_1392_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1399_, 0, v_declName_1391_);
lean_closure_set(v___f_1399_, 1, v___x_1398_);
v___x_1400_ = 0;
v___x_1401_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(v___f_1399_, v___x_1400_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* v_declName_1402_, lean_object* v_kind_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
uint8_t v_kind_boxed_1409_; lean_object* v_res_1410_; 
v_kind_boxed_1409_ = lean_unbox(v_kind_1403_);
v_res_1410_ = l_Lean_Meta_addUnificationHint(v_declName_1402_, v_kind_boxed_1409_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(lean_object* v_00_u03b1_1411_, lean_object* v_constName_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1419_, lean_object* v_constName_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(v_00_u03b1_1419_, v_constName_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1427_, lean_object* v_ref_1428_, lean_object* v_constName_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_1428_, v_constName_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1436_, lean_object* v_ref_1437_, lean_object* v_constName_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(v_00_u03b1_1436_, v_ref_1437_, v_constName_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v_ref_1437_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_1445_, lean_object* v_ref_1446_, lean_object* v_msg_1447_, lean_object* v_declHint_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_1446_, v_msg_1447_, v_declHint_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1455_, lean_object* v_ref_1456_, lean_object* v_msg_1457_, lean_object* v_declHint_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(v_00_u03b1_1455_, v_ref_1456_, v_msg_1457_, v_declHint_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v_ref_1456_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1465_, lean_object* v_declHint_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1465_, v_declHint_1466_, v___y_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1473_, lean_object* v_declHint_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(v_msg_1473_, v_declHint_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1481_, lean_object* v_ref_1482_, lean_object* v_msg_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_1482_, v_msg_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1490_, lean_object* v_ref_1491_, lean_object* v_msg_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(v_00_u03b1_1490_, v_ref_1491_, v_msg_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v_ref_1491_);
return v_res_1498_;
}
}
static uint64_t _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1505_; uint64_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1506_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_uint64_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1508_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1509_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set_uint64(v___x_1509_, sizeof(void*)*1, v___x_1507_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1510_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1514_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
lean_ctor_set(v___x_1514_, 2, v___x_1513_);
lean_ctor_set(v___x_1514_, 3, v___x_1513_);
lean_ctor_set(v___x_1514_, 4, v___x_1513_);
lean_ctor_set(v___x_1514_, 5, v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
lean_ctor_set(v___x_1516_, 2, v___x_1515_);
lean_ctor_set(v___x_1516_, 3, v___x_1515_);
lean_ctor_set(v___x_1516_, 4, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1517_, lean_object* v___x_1518_, lean_object* v_declName_1519_, lean_object* v_stx_1520_, uint8_t v_kind_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1520_, v___y_1522_, v___y_1523_);
if (lean_obj_tag(v___x_1525_) == 0)
{
uint8_t v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; size_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec_ref_known(v___x_1525_, 1);
v___x_1526_ = 0;
v___x_1527_ = 1;
v___x_1528_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1529_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1530_ = lean_unsigned_to_nat(32u);
v___x_1531_ = lean_mk_empty_array_with_capacity(v___x_1530_);
v___x_1532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1533_ = ((size_t)5ULL);
lean_inc_n(v___x_1517_, 6);
v___x_1534_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1531_);
lean_ctor_set(v___x_1534_, 2, v___x_1517_);
lean_ctor_set(v___x_1534_, 3, v___x_1517_);
lean_ctor_set_usize(v___x_1534_, 4, v___x_1533_);
v___x_1535_ = lean_box(1);
lean_inc_ref(v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1529_);
lean_ctor_set(v___x_1536_, 1, v___x_1534_);
lean_ctor_set(v___x_1536_, 2, v___x_1535_);
v___x_1537_ = lean_mk_empty_array_with_capacity(v___x_1517_);
v___x_1538_ = lean_box(0);
lean_inc(v___x_1518_);
v___x_1539_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1539_, 0, v___x_1528_);
lean_ctor_set(v___x_1539_, 1, v___x_1518_);
lean_ctor_set(v___x_1539_, 2, v___x_1536_);
lean_ctor_set(v___x_1539_, 3, v___x_1537_);
lean_ctor_set(v___x_1539_, 4, v___x_1538_);
lean_ctor_set(v___x_1539_, 5, v___x_1517_);
lean_ctor_set(v___x_1539_, 6, v___x_1538_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*7, v___x_1526_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*7 + 1, v___x_1526_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*7 + 2, v___x_1526_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*7 + 3, v___x_1527_);
v___x_1540_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1517_);
lean_ctor_set(v___x_1540_, 1, v___x_1517_);
lean_ctor_set(v___x_1540_, 2, v___x_1517_);
lean_ctor_set(v___x_1540_, 3, v___x_1517_);
lean_ctor_set(v___x_1540_, 4, v___x_1529_);
lean_ctor_set(v___x_1540_, 5, v___x_1529_);
lean_ctor_set(v___x_1540_, 6, v___x_1529_);
lean_ctor_set(v___x_1540_, 7, v___x_1529_);
lean_ctor_set(v___x_1540_, 8, v___x_1529_);
lean_ctor_set(v___x_1540_, 9, v___x_1529_);
lean_ctor_set(v___x_1540_, 10, v___x_1529_);
v___x_1541_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1542_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1540_);
lean_ctor_set(v___x_1543_, 1, v___x_1541_);
lean_ctor_set(v___x_1543_, 2, v___x_1518_);
lean_ctor_set(v___x_1543_, 3, v___x_1534_);
lean_ctor_set(v___x_1543_, 4, v___x_1542_);
v___x_1544_ = lean_st_mk_ref(v___x_1543_);
v___x_1545_ = l_Lean_Meta_addUnificationHint(v_declName_1519_, v_kind_1521_, v___x_1539_, v___x_1544_, v___y_1522_, v___y_1523_);
lean_dec_ref_known(v___x_1539_, 7);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1554_; 
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v___x_1545_, 0);
lean_dec(v_unused_1555_);
v___x_1547_ = v___x_1545_;
v_isShared_1548_ = v_isSharedCheck_1554_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v___x_1545_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1554_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1549_ = lean_st_ref_get(v___x_1544_);
lean_dec(v___x_1544_);
lean_dec(v___x_1549_);
v___x_1550_ = lean_box(0);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1550_);
v___x_1552_ = v___x_1547_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_dec(v___x_1544_);
return v___x_1545_;
}
}
else
{
lean_dec(v_declName_1519_);
lean_dec(v___x_1518_);
lean_dec(v___x_1517_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1556_, lean_object* v___x_1557_, lean_object* v_declName_1558_, lean_object* v_stx_1559_, lean_object* v_kind_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
uint8_t v_kind_boxed_1564_; lean_object* v_res_1565_; 
v_kind_boxed_1564_ = lean_unbox(v_kind_1560_);
v_res_1565_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1556_, v___x_1557_, v_declName_1558_, v_stx_1559_, v_kind_boxed_1564_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; lean_object* v_env_1571_; lean_object* v_options_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1570_ = lean_st_ref_get(v___y_1568_);
v_env_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_ref(v_env_1571_);
lean_dec(v___x_1570_);
v_options_1572_ = lean_ctor_get(v___y_1567_, 1);
v___x_1573_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1574_ = lean_unsigned_to_nat(32u);
v___x_1575_ = lean_mk_empty_array_with_capacity(v___x_1574_);
lean_dec_ref(v___x_1575_);
v___x_1576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_1572_);
v___x_1577_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1577_, 0, v_env_1571_);
lean_ctor_set(v___x_1577_, 1, v___x_1573_);
lean_ctor_set(v___x_1577_, 2, v___x_1576_);
lean_ctor_set(v___x_1577_, 3, v_options_1572_);
v___x_1578_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_msgData_1566_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_ref_1589_; lean_object* v___x_1590_; lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
v_ref_1589_ = lean_ctor_get(v___y_1586_, 4);
v___x_1590_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msg_1585_, v___y_1586_, v___y_1587_);
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_inc(v_ref_1589_);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_ref_1589_);
lean_ctor_set(v___x_1595_, 1, v_a_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set_tag(v___x_1593_, 1);
lean_ctor_set(v___x_1593_, 0, v___x_1595_);
v___x_1597_ = v___x_1593_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
return v_res_1604_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
return v___x_1607_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(lean_object* v___x_1611_, lean_object* v_decl_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1617_ = l_Lean_MessageData_ofName(v___x_1611_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v___x_1620_, v___y_1613_, v___y_1614_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v___x_1622_, lean_object* v_decl_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_1622_, v_decl_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v_decl_1623_);
return v_res_1627_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = lean_unsigned_to_nat(3033092106u);
v___x_1672_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1673_ = l_Lean_Name_num___override(v___x_1672_, v___x_1671_);
return v___x_1673_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1676_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1677_ = l_Lean_Name_str___override(v___x_1676_, v___x_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1680_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1681_ = l_Lean_Name_str___override(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_unsigned_to_nat(2u);
v___x_1683_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1684_ = l_Lean_Name_num___override(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1691_ = 0;
v___x_1692_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1693_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1695_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___x_1693_);
lean_ctor_set(v___x_1695_, 2, v___x_1692_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*3, v___x_1691_);
return v___x_1695_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___f_1696_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___f_1697_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_1698_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v___f_1697_);
lean_ctor_set(v___x_1699_, 2, v___f_1696_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
v___x_1702_ = l_Lean_registerBuiltinAttribute(v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1705_, lean_object* v_msg_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_1706_, v___y_1707_, v___y_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1711_, lean_object* v_msg_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(v_00_u03b1_1711_, v_msg_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* v_p_1717_, lean_object* v_e_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v___y_1725_; lean_object* v___x_1742_; uint8_t v_transparency_1743_; uint8_t v___x_1744_; uint8_t v___x_1745_; 
v___x_1742_ = l_Lean_Meta_Context_config(v_a_1719_);
v_transparency_1743_ = lean_ctor_get_uint8(v___x_1742_, 9);
lean_dec_ref(v___x_1742_);
v___x_1744_ = 2;
v___x_1745_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1743_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v_keyedConfig_1746_; uint8_t v_trackZetaDelta_1747_; lean_object* v_zetaDeltaSet_1748_; lean_object* v_lctx_1749_; lean_object* v_localInstances_1750_; lean_object* v_defEqCtx_x3f_1751_; lean_object* v_synthPendingDepth_1752_; lean_object* v_customCanUnfoldPredicate_x3f_1753_; uint8_t v_univApprox_1754_; uint8_t v_inTypeClassResolution_1755_; uint8_t v_cacheInferType_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_keyedConfig_1746_ = lean_ctor_get(v_a_1719_, 0);
v_trackZetaDelta_1747_ = lean_ctor_get_uint8(v_a_1719_, sizeof(void*)*7);
v_zetaDeltaSet_1748_ = lean_ctor_get(v_a_1719_, 1);
v_lctx_1749_ = lean_ctor_get(v_a_1719_, 2);
v_localInstances_1750_ = lean_ctor_get(v_a_1719_, 3);
v_defEqCtx_x3f_1751_ = lean_ctor_get(v_a_1719_, 4);
v_synthPendingDepth_1752_ = lean_ctor_get(v_a_1719_, 5);
v_customCanUnfoldPredicate_x3f_1753_ = lean_ctor_get(v_a_1719_, 6);
v_univApprox_1754_ = lean_ctor_get_uint8(v_a_1719_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1755_ = lean_ctor_get_uint8(v_a_1719_, sizeof(void*)*7 + 2);
v_cacheInferType_1756_ = lean_ctor_get_uint8(v_a_1719_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1746_);
v___x_1757_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1744_, v_keyedConfig_1746_);
lean_inc(v_customCanUnfoldPredicate_x3f_1753_);
lean_inc(v_synthPendingDepth_1752_);
lean_inc(v_defEqCtx_x3f_1751_);
lean_inc_ref(v_localInstances_1750_);
lean_inc_ref(v_lctx_1749_);
lean_inc(v_zetaDeltaSet_1748_);
v___x_1758_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v_zetaDeltaSet_1748_);
lean_ctor_set(v___x_1758_, 2, v_lctx_1749_);
lean_ctor_set(v___x_1758_, 3, v_localInstances_1750_);
lean_ctor_set(v___x_1758_, 4, v_defEqCtx_x3f_1751_);
lean_ctor_set(v___x_1758_, 5, v_synthPendingDepth_1752_);
lean_ctor_set(v___x_1758_, 6, v_customCanUnfoldPredicate_x3f_1753_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*7, v_trackZetaDelta_1747_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*7 + 1, v_univApprox_1754_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1755_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*7 + 3, v_cacheInferType_1756_);
lean_inc(v_a_1722_);
lean_inc_ref(v_a_1721_);
lean_inc(v_a_1720_);
v___x_1759_ = lean_is_expr_def_eq(v_p_1717_, v_e_1718_, v___x_1758_, v_a_1720_, v_a_1721_, v_a_1722_);
v___y_1725_ = v___x_1759_;
goto v___jp_1724_;
}
else
{
lean_object* v___x_1760_; 
lean_inc(v_a_1722_);
lean_inc_ref(v_a_1721_);
lean_inc(v_a_1720_);
lean_inc_ref(v_a_1719_);
v___x_1760_ = lean_is_expr_def_eq(v_p_1717_, v_e_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
v___y_1725_ = v___x_1760_;
goto v___jp_1724_;
}
v___jp_1724_:
{
if (lean_obj_tag(v___y_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_a_1726_ = lean_ctor_get(v___y_1725_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___y_1725_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___y_1725_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___y_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
v_a_1734_ = lean_ctor_get(v___y_1725_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___y_1725_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___y_1725_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___y_1725_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object* v_p_1761_, lean_object* v_e_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_p_1761_, v_e_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object* v_x_1769_, lean_object* v_x_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
if (lean_obj_tag(v_x_1769_) == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = l_List_reverse___redArg(v_x_1770_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
else
{
lean_object* v_tail_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1796_; 
v_tail_1778_ = lean_ctor_get(v_x_1769_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1769_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v_x_1769_, 0);
lean_dec(v_unused_1797_);
v___x_1780_ = v_x_1769_;
v_isShared_1781_ = v_isSharedCheck_1796_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_tail_1778_);
lean_dec(v_x_1769_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1796_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v_x_1770_);
lean_ctor_set(v___x_1780_, 0, v_a_1783_);
v___x_1785_ = v___x_1780_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1783_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_x_1770_);
v___x_1785_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
v_x_1769_ = v_tail_1778_;
v_x_1770_ = v___x_1785_;
goto _start;
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_del_object(v___x_1780_);
lean_dec(v_tail_1778_);
lean_dec(v_x_1770_);
v_a_1788_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1782_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1782_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object* v_x_1798_, lean_object* v_x_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v_x_1798_, v_x_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1805_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1806_; double v___x_1807_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_float_of_nat(v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object* v_cls_1811_, lean_object* v_msg_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_ref_1818_; lean_object* v___x_1819_; lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1864_; 
v_ref_1818_ = lean_ctor_get(v___y_1815_, 4);
v___x_1819_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1864_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1864_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v_traceState_1825_; lean_object* v_env_1826_; lean_object* v_nextMacroScope_1827_; lean_object* v_ngen_1828_; lean_object* v_auxDeclNGen_1829_; lean_object* v_cache_1830_; lean_object* v_messages_1831_; lean_object* v_infoState_1832_; lean_object* v_snapshotTasks_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1863_; 
v___x_1824_ = lean_st_ref_take(v___y_1816_);
v_traceState_1825_ = lean_ctor_get(v___x_1824_, 4);
v_env_1826_ = lean_ctor_get(v___x_1824_, 0);
v_nextMacroScope_1827_ = lean_ctor_get(v___x_1824_, 1);
v_ngen_1828_ = lean_ctor_get(v___x_1824_, 2);
v_auxDeclNGen_1829_ = lean_ctor_get(v___x_1824_, 3);
v_cache_1830_ = lean_ctor_get(v___x_1824_, 5);
v_messages_1831_ = lean_ctor_get(v___x_1824_, 6);
v_infoState_1832_ = lean_ctor_get(v___x_1824_, 7);
v_snapshotTasks_1833_ = lean_ctor_get(v___x_1824_, 8);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1835_ = v___x_1824_;
v_isShared_1836_ = v_isSharedCheck_1863_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_snapshotTasks_1833_);
lean_inc(v_infoState_1832_);
lean_inc(v_messages_1831_);
lean_inc(v_cache_1830_);
lean_inc(v_traceState_1825_);
lean_inc(v_auxDeclNGen_1829_);
lean_inc(v_ngen_1828_);
lean_inc(v_nextMacroScope_1827_);
lean_inc(v_env_1826_);
lean_dec(v___x_1824_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1863_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
uint64_t v_tid_1837_; lean_object* v_traces_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1862_; 
v_tid_1837_ = lean_ctor_get_uint64(v_traceState_1825_, sizeof(void*)*1);
v_traces_1838_ = lean_ctor_get(v_traceState_1825_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_traceState_1825_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1840_ = v_traceState_1825_;
v_isShared_1841_ = v_isSharedCheck_1862_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_traces_1838_);
lean_dec(v_traceState_1825_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1862_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; double v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1842_ = lean_box(0);
v___x_1843_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
v___x_1844_ = 0;
v___x_1845_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_1846_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1846_, 0, v_cls_1811_);
lean_ctor_set(v___x_1846_, 1, v___x_1842_);
lean_ctor_set(v___x_1846_, 2, v___x_1845_);
lean_ctor_set_float(v___x_1846_, sizeof(void*)*3, v___x_1843_);
lean_ctor_set_float(v___x_1846_, sizeof(void*)*3 + 8, v___x_1843_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*3 + 16, v___x_1844_);
v___x_1847_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2));
v___x_1848_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v_a_1820_);
lean_ctor_set(v___x_1848_, 2, v___x_1847_);
lean_inc(v_ref_1818_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v_ref_1818_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_PersistentArray_push___redArg(v_traces_1838_, v___x_1849_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1850_);
v___x_1852_ = v___x_1840_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1850_);
lean_ctor_set_uint64(v_reuseFailAlloc_1861_, sizeof(void*)*1, v_tid_1837_);
v___x_1852_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 4, v___x_1852_);
v___x_1854_ = v___x_1835_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_env_1826_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_nextMacroScope_1827_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_ngen_1828_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_auxDeclNGen_1829_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1860_, 5, v_cache_1830_);
lean_ctor_set(v_reuseFailAlloc_1860_, 6, v_messages_1831_);
lean_ctor_set(v_reuseFailAlloc_1860_, 7, v_infoState_1832_);
lean_ctor_set(v_reuseFailAlloc_1860_, 8, v_snapshotTasks_1833_);
v___x_1854_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1855_ = lean_st_ref_put(v___y_1816_, v___x_1854_);
v___x_1856_ = lean_box(0);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1856_);
v___x_1858_ = v___x_1822_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object* v_cls_1865_, lean_object* v_msg_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_1865_, v_msg_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object* v_as_1876_, size_t v_sz_1877_, size_t v_i_1878_, lean_object* v_b_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_a_1886_; uint8_t v___x_1890_; 
v___x_1890_ = lean_usize_dec_lt(v_i_1878_, v_sz_1877_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_b_1879_);
return v___x_1891_;
}
else
{
lean_object* v_snd_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1982_; 
v_snd_1892_ = lean_ctor_get(v_b_1879_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_b_1879_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_b_1879_, 0);
lean_dec(v_unused_1983_);
v___x_1894_ = v_b_1879_;
v_isShared_1895_ = v_isSharedCheck_1982_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_snd_1892_);
lean_dec(v_b_1879_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1982_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v_array_1896_; lean_object* v_start_1897_; lean_object* v_stop_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v_array_1896_ = lean_ctor_get(v_snd_1892_, 0);
v_start_1897_ = lean_ctor_get(v_snd_1892_, 1);
v_stop_1898_ = lean_ctor_get(v_snd_1892_, 2);
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_nat_dec_lt(v_start_1897_, v_stop_1898_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1902_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1899_);
v___x_1902_ = v___x_1894_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_snd_1892_);
v___x_1902_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
}
else
{
lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1978_; 
lean_inc(v_stop_1898_);
lean_inc(v_start_1897_);
lean_inc_ref(v_array_1896_);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_snd_1892_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; lean_object* v_unused_1980_; lean_object* v_unused_1981_; 
v_unused_1979_ = lean_ctor_get(v_snd_1892_, 2);
lean_dec(v_unused_1979_);
v_unused_1980_ = lean_ctor_get(v_snd_1892_, 1);
lean_dec(v_unused_1980_);
v_unused_1981_ = lean_ctor_get(v_snd_1892_, 0);
lean_dec(v_unused_1981_);
v___x_1906_ = v_snd_1892_;
v_isShared_1907_ = v_isSharedCheck_1978_;
goto v_resetjp_1905_;
}
else
{
lean_dec(v_snd_1892_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1978_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1908_ = lean_array_fget(v_array_1896_, v_start_1897_);
v___x_1909_ = lean_unsigned_to_nat(1u);
v___x_1910_ = lean_nat_add(v_start_1897_, v___x_1909_);
lean_dec(v_start_1897_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 1, v___x_1910_);
v___x_1912_ = v___x_1906_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_array_1896_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_stop_1898_);
v___x_1912_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
uint8_t v___x_1913_; uint8_t v___x_1914_; uint8_t v___x_1915_; 
v___x_1913_ = 3;
v___x_1914_ = lean_unbox(v___x_1908_);
lean_dec(v___x_1908_);
v___x_1915_ = l_Lean_instBEqBinderInfo_beq(v___x_1914_, v___x_1913_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1917_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1912_);
lean_ctor_set(v___x_1894_, 0, v___x_1899_);
v___x_1917_ = v___x_1894_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
v_a_1886_ = v___x_1917_;
goto v___jp_1885_;
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1919_ = lean_array_uget_borrowed(v_as_1876_, v_i_1878_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
lean_inc(v_a_1919_);
v___x_1920_ = lean_infer_type(v_a_1919_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = l_Lean_Meta_trySynthInstance(v_a_1921_, v___x_1899_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1960_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1960_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1960_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
if (lean_obj_tag(v_a_1923_) == 1)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
lean_del_object(v___x_1925_);
v_a_1927_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v_a_1923_, 1);
lean_inc(v_a_1919_);
v___x_1928_ = l_Lean_Meta_isExprDefEq(v_a_1919_, v_a_1927_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1944_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1944_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1944_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_unbox(v_a_1929_);
lean_dec(v_a_1929_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1912_);
lean_ctor_set(v___x_1894_, 0, v___x_1934_);
v___x_1936_ = v___x_1894_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1912_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1936_);
v___x_1938_ = v___x_1931_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
lean_object* v___x_1942_; 
lean_del_object(v___x_1931_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1912_);
lean_ctor_set(v___x_1894_, 0, v___x_1899_);
v___x_1942_ = v___x_1894_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___x_1912_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_a_1886_ = v___x_1942_;
goto v___jp_1885_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v___x_1912_);
lean_del_object(v___x_1894_);
v_a_1945_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1928_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1928_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
lean_dec(v_a_1923_);
v___x_1953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0));
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1912_);
lean_ctor_set(v___x_1894_, 0, v___x_1953_);
v___x_1955_ = v___x_1894_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1912_);
v___x_1955_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1955_);
v___x_1957_ = v___x_1925_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v___x_1912_);
lean_del_object(v___x_1894_);
v_a_1961_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1922_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1922_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v___x_1912_);
lean_del_object(v___x_1894_);
v_a_1969_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1920_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1920_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
}
}
}
}
v___jp_1885_:
{
size_t v___x_1887_; size_t v___x_1888_; 
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1878_, v___x_1887_);
v_i_1878_ = v___x_1888_;
v_b_1879_ = v_a_1886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object* v_as_1984_, lean_object* v_sz_1985_, lean_object* v_i_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
size_t v_sz_boxed_1993_; size_t v_i_boxed_1994_; lean_object* v_res_1995_; 
v_sz_boxed_1993_ = lean_unbox_usize(v_sz_1985_);
lean_dec(v_sz_1985_);
v_i_boxed_1994_ = lean_unbox_usize(v_i_1986_);
lean_dec(v_i_1986_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_as_1984_, v_sz_boxed_1993_, v_i_boxed_1994_, v_b_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v_as_1984_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object* v_as_x27_1999_, lean_object* v_b_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
if (lean_obj_tag(v_as_x27_1999_) == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_b_2000_);
return v___x_2006_;
}
else
{
lean_object* v_head_2007_; lean_object* v_tail_2008_; lean_object* v_lhs_2009_; lean_object* v_rhs_2010_; lean_object* v___x_2011_; 
lean_dec_ref(v_b_2000_);
v_head_2007_ = lean_ctor_get(v_as_x27_1999_, 0);
v_tail_2008_ = lean_ctor_get(v_as_x27_1999_, 1);
v_lhs_2009_ = lean_ctor_get(v_head_2007_, 0);
v_rhs_2010_ = lean_ctor_get(v_head_2007_, 1);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc_ref(v___y_2001_);
lean_inc_ref(v_rhs_2010_);
lean_inc_ref(v_lhs_2009_);
v___x_2011_ = lean_is_expr_def_eq(v_lhs_2009_, v_rhs_2010_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2025_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2025_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2025_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_unbox(v_a_2012_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_a_2012_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v___x_2016_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2019_);
v___x_2021_ = v___x_2014_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
else
{
lean_object* v___x_2023_; 
lean_del_object(v___x_2014_);
lean_dec(v_a_2012_);
v___x_2023_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_as_x27_1999_ = v_tail_2008_;
v_b_2000_ = v___x_2023_;
goto _start;
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_a_2026_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2011_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2011_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(lean_object* v_as_x27_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2034_, v_b_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v_as_x27_2034_);
return v_res_2041_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2042_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0);
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
return v___x_2044_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8(void){
_start:
{
lean_object* v_cls_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_cls_2057_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2058_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7));
v___x_2059_ = l_Lean_Name_append(v___x_2058_, v_cls_2057_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9));
v___x_2062_ = l_Lean_stringToMessageData(v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(lean_object* v_candidate_2063_, lean_object* v_t_2064_, lean_object* v_s_2065_, uint8_t v_mayPostpone_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Meta_saveState___redArg(v_a_2068_, v_a_2070_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2325_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2325_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2325_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___y_2078_; uint8_t v___y_2079_; lean_object* v_a_2101_; uint8_t v_a_2105_; lean_object* v___x_2117_; lean_object* v_cache_2118_; lean_object* v_mctx_2119_; lean_object* v_zetaDeltaFVarIds_2120_; lean_object* v_postponed_2121_; lean_object* v_diag_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2324_; 
v___x_2117_ = lean_st_ref_take(v_a_2068_);
v_cache_2118_ = lean_ctor_get(v___x_2117_, 1);
v_mctx_2119_ = lean_ctor_get(v___x_2117_, 0);
v_zetaDeltaFVarIds_2120_ = lean_ctor_get(v___x_2117_, 2);
v_postponed_2121_ = lean_ctor_get(v___x_2117_, 3);
v_diag_2122_ = lean_ctor_get(v___x_2117_, 4);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2124_ = v___x_2117_;
v_isShared_2125_ = v_isSharedCheck_2324_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_diag_2122_);
lean_inc(v_postponed_2121_);
lean_inc(v_zetaDeltaFVarIds_2120_);
lean_inc(v_cache_2118_);
lean_inc(v_mctx_2119_);
lean_dec(v___x_2117_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2324_;
goto v_resetjp_2123_;
}
v___jp_2077_:
{
if (v___y_2079_ == 0)
{
lean_object* v___x_2080_; 
lean_del_object(v___x_2075_);
v___x_2080_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2073_, v_a_2068_, v_a_2070_);
lean_dec(v_a_2073_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2080_, 0);
lean_dec(v_unused_2088_);
v___x_2082_ = v___x_2080_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_dec(v___x_2080_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 1);
lean_ctor_set(v___x_2082_, 0, v___y_2078_);
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___y_2078_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v___y_2078_);
v_a_2089_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2080_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2080_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v___x_2098_; 
lean_dec(v_a_2073_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 1);
lean_ctor_set(v___x_2075_, 0, v___y_2078_);
v___x_2098_ = v___x_2075_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___y_2078_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
v___jp_2100_:
{
uint8_t v___x_2102_; 
v___x_2102_ = l_Lean_Exception_isInterrupt(v_a_2101_);
if (v___x_2102_ == 0)
{
uint8_t v___x_2103_; 
lean_inc_ref(v_a_2101_);
v___x_2103_ = l_Lean_Exception_isRuntime(v_a_2101_);
v___y_2078_ = v_a_2101_;
v___y_2079_ = v___x_2103_;
goto v___jp_2077_;
}
else
{
v___y_2078_ = v_a_2101_;
v___y_2079_ = v___x_2102_;
goto v___jp_2077_;
}
}
v___jp_2104_:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2073_, v_a_2068_, v_a_2070_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2114_; 
lean_del_object(v___x_2075_);
lean_dec(v_a_2073_);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v___x_2106_, 0);
lean_dec(v_unused_2115_);
v___x_2108_ = v___x_2106_;
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v___x_2106_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_box(v_a_2105_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2110_);
v___x_2112_ = v___x_2108_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
else
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2106_, 1);
v_a_2101_ = v_a_2116_;
goto v___jp_2100_;
}
}
v_resetjp_2123_:
{
lean_object* v_inferType_2126_; lean_object* v_funInfo_2127_; lean_object* v_synthInstance_2128_; lean_object* v_whnf_2129_; lean_object* v_defEqPerm_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2322_; 
v_inferType_2126_ = lean_ctor_get(v_cache_2118_, 0);
v_funInfo_2127_ = lean_ctor_get(v_cache_2118_, 1);
v_synthInstance_2128_ = lean_ctor_get(v_cache_2118_, 2);
v_whnf_2129_ = lean_ctor_get(v_cache_2118_, 3);
v_defEqPerm_2130_ = lean_ctor_get(v_cache_2118_, 5);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_cache_2118_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v_cache_2118_, 4);
lean_dec(v_unused_2323_);
v___x_2132_ = v_cache_2118_;
v_isShared_2133_ = v_isSharedCheck_2322_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_defEqPerm_2130_);
lean_inc(v_whnf_2129_);
lean_inc(v_synthInstance_2128_);
lean_inc(v_funInfo_2127_);
lean_inc(v_inferType_2126_);
lean_dec(v_cache_2118_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2322_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v___x_2134_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_inferType_2126_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_funInfo_2127_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_synthInstance_2128_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_whnf_2129_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2321_, 5, v_defEqPerm_2130_);
v___x_2136_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2138_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v___x_2136_);
v___x_2138_ = v___x_2124_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_mctx_2119_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_zetaDeltaFVarIds_2120_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_postponed_2121_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_diag_2122_);
v___x_2138_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_st_ref_put(v_a_2068_, v___x_2138_);
v___x_2140_ = l_Lean_Meta_getResetPostponed___redArg(v_a_2068_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; uint8_t v_a_2143_; lean_object* v___x_2184_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
lean_inc(v_candidate_2063_);
v___x_2184_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(v_candidate_2063_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = l_Lean_ConstantInfo_levelParams(v_a_2185_);
v___x_2187_ = lean_box(0);
v___x_2188_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v___x_2186_, v___x_2187_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = 0;
v___x_2191_ = l_Lean_Core_instantiateValueLevelParams(v_a_2185_, v_a_2189_, v___x_2190_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2185_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2193_ = lean_box(0);
v___x_2194_ = l_Lean_Meta_lambdaMetaTelescope(v_a_2192_, v___x_2193_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2192_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v_snd_2196_; lean_object* v_fst_2197_; lean_object* v_fst_2198_; lean_object* v_snd_2199_; lean_object* v___x_2200_; uint8_t v_foApprox_2201_; uint8_t v_ctxApprox_2202_; uint8_t v_quasiPatternApprox_2203_; uint8_t v_constApprox_2204_; uint8_t v_isDefEqStuckEx_2205_; uint8_t v_proofIrrelevance_2206_; uint8_t v_assignSyntheticOpaque_2207_; uint8_t v_offsetCnstrs_2208_; uint8_t v_transparency_2209_; uint8_t v_etaStruct_2210_; uint8_t v_univApprox_2211_; uint8_t v_iota_2212_; uint8_t v_beta_2213_; uint8_t v_proj_2214_; uint8_t v_zeta_2215_; uint8_t v_zetaDelta_2216_; uint8_t v_zetaUnused_2217_; uint8_t v_zetaHave_2218_; uint8_t v_canUnfoldPredicateConfig_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2307_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v_snd_2196_ = lean_ctor_get(v_a_2195_, 1);
lean_inc(v_snd_2196_);
v_fst_2197_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_fst_2197_);
lean_dec(v_a_2195_);
v_fst_2198_ = lean_ctor_get(v_snd_2196_, 0);
lean_inc(v_fst_2198_);
v_snd_2199_ = lean_ctor_get(v_snd_2196_, 1);
lean_inc(v_snd_2199_);
lean_dec(v_snd_2196_);
v___x_2200_ = l_Lean_Meta_Context_config(v_a_2067_);
v_foApprox_2201_ = lean_ctor_get_uint8(v___x_2200_, 0);
v_ctxApprox_2202_ = lean_ctor_get_uint8(v___x_2200_, 1);
v_quasiPatternApprox_2203_ = lean_ctor_get_uint8(v___x_2200_, 2);
v_constApprox_2204_ = lean_ctor_get_uint8(v___x_2200_, 3);
v_isDefEqStuckEx_2205_ = lean_ctor_get_uint8(v___x_2200_, 4);
v_proofIrrelevance_2206_ = lean_ctor_get_uint8(v___x_2200_, 6);
v_assignSyntheticOpaque_2207_ = lean_ctor_get_uint8(v___x_2200_, 7);
v_offsetCnstrs_2208_ = lean_ctor_get_uint8(v___x_2200_, 8);
v_transparency_2209_ = lean_ctor_get_uint8(v___x_2200_, 9);
v_etaStruct_2210_ = lean_ctor_get_uint8(v___x_2200_, 10);
v_univApprox_2211_ = lean_ctor_get_uint8(v___x_2200_, 11);
v_iota_2212_ = lean_ctor_get_uint8(v___x_2200_, 12);
v_beta_2213_ = lean_ctor_get_uint8(v___x_2200_, 13);
v_proj_2214_ = lean_ctor_get_uint8(v___x_2200_, 14);
v_zeta_2215_ = lean_ctor_get_uint8(v___x_2200_, 15);
v_zetaDelta_2216_ = lean_ctor_get_uint8(v___x_2200_, 16);
v_zetaUnused_2217_ = lean_ctor_get_uint8(v___x_2200_, 17);
v_zetaHave_2218_ = lean_ctor_get_uint8(v___x_2200_, 18);
v_canUnfoldPredicateConfig_2219_ = lean_ctor_get_uint8(v___x_2200_, 19);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2221_ = v___x_2200_;
v_isShared_2222_ = v_isSharedCheck_2307_;
goto v_resetjp_2220_;
}
else
{
lean_dec(v___x_2200_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2307_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_2199_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_dec_ref_known(v___x_2223_, 1);
lean_del_object(v___x_2221_);
lean_dec(v_fst_2198_);
lean_dec(v_fst_2197_);
lean_dec(v_a_2141_);
lean_dec_ref(v_s_2065_);
lean_dec_ref(v_t_2064_);
lean_dec(v_candidate_2063_);
v_a_2105_ = v___x_2190_;
goto v___jp_2104_;
}
else
{
lean_object* v_a_2224_; uint8_t v_trackZetaDelta_2225_; lean_object* v_zetaDeltaSet_2226_; lean_object* v_lctx_2227_; lean_object* v_localInstances_2228_; lean_object* v_defEqCtx_x3f_2229_; lean_object* v_synthPendingDepth_2230_; lean_object* v_customCanUnfoldPredicate_x3f_2231_; uint8_t v_univApprox_2232_; uint8_t v_inTypeClassResolution_2233_; uint8_t v_cacheInferType_2234_; lean_object* v_pattern_2235_; lean_object* v_constraints_2236_; uint8_t v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v_lhs_2269_; lean_object* v_rhs_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2306_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v_trackZetaDelta_2225_ = lean_ctor_get_uint8(v_a_2067_, sizeof(void*)*7);
v_zetaDeltaSet_2226_ = lean_ctor_get(v_a_2067_, 1);
v_lctx_2227_ = lean_ctor_get(v_a_2067_, 2);
v_localInstances_2228_ = lean_ctor_get(v_a_2067_, 3);
v_defEqCtx_x3f_2229_ = lean_ctor_get(v_a_2067_, 4);
v_synthPendingDepth_2230_ = lean_ctor_get(v_a_2067_, 5);
v_customCanUnfoldPredicate_x3f_2231_ = lean_ctor_get(v_a_2067_, 6);
v_univApprox_2232_ = lean_ctor_get_uint8(v_a_2067_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2233_ = lean_ctor_get_uint8(v_a_2067_, sizeof(void*)*7 + 2);
v_cacheInferType_2234_ = lean_ctor_get_uint8(v_a_2067_, sizeof(void*)*7 + 3);
v_pattern_2235_ = lean_ctor_get(v_a_2224_, 0);
lean_inc_ref(v_pattern_2235_);
v_constraints_2236_ = lean_ctor_get(v_a_2224_, 1);
lean_inc(v_constraints_2236_);
lean_dec(v_a_2224_);
v_lhs_2269_ = lean_ctor_get(v_pattern_2235_, 0);
v_rhs_2270_ = lean_ctor_get(v_pattern_2235_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_pattern_2235_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2272_ = v_pattern_2235_;
v_isShared_2273_ = v_isSharedCheck_2306_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_rhs_2270_);
lean_inc(v_lhs_2269_);
lean_dec(v_pattern_2235_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2306_;
goto v_resetjp_2271_;
}
v___jp_2237_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2));
v___x_2244_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_constraints_2236_, v___x_2243_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v_constraints_2236_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v_fst_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2266_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
v_fst_2246_ = lean_ctor_get(v_a_2245_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_a_2245_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; 
v_unused_2267_ = lean_ctor_get(v_a_2245_, 1);
lean_dec(v_unused_2267_);
v___x_2248_ = v_a_2245_;
v_isShared_2249_ = v_isSharedCheck_2266_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_fst_2246_);
lean_dec(v_a_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2266_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
if (lean_obj_tag(v_fst_2246_) == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = lean_array_get_size(v_fst_2198_);
v___x_2252_ = l_Array_toSubarray___redArg(v_fst_2198_, v___x_2250_, v___x_2251_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v___x_2252_);
lean_ctor_set(v___x_2248_, 0, v___x_2193_);
v___x_2254_ = v___x_2248_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
size_t v_sz_2255_; size_t v___x_2256_; lean_object* v___x_2257_; 
v_sz_2255_ = lean_array_size(v_fst_2197_);
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_fst_2197_, v_sz_2255_, v___x_2256_, v___x_2254_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v_fst_2197_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v_fst_2259_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v_fst_2259_ = lean_ctor_get(v_a_2258_, 0);
lean_inc(v_fst_2259_);
lean_dec(v_a_2258_);
if (lean_obj_tag(v_fst_2259_) == 0)
{
v_a_2143_ = v___y_2238_;
goto v___jp_2142_;
}
else
{
lean_object* v_val_2260_; uint8_t v___x_2261_; 
v_val_2260_ = lean_ctor_get(v_fst_2259_, 0);
lean_inc(v_val_2260_);
lean_dec_ref_known(v_fst_2259_, 1);
v___x_2261_ = lean_unbox(v_val_2260_);
lean_dec(v_val_2260_);
v_a_2143_ = v___x_2261_;
goto v___jp_2142_;
}
}
else
{
lean_object* v_a_2262_; 
lean_dec(v_a_2141_);
v_a_2262_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2257_, 1);
v_a_2101_ = v_a_2262_;
goto v___jp_2100_;
}
}
}
else
{
lean_object* v_val_2264_; uint8_t v___x_2265_; 
lean_del_object(v___x_2248_);
lean_dec(v_fst_2198_);
lean_dec(v_fst_2197_);
v_val_2264_ = lean_ctor_get(v_fst_2246_, 0);
lean_inc(v_val_2264_);
lean_dec_ref_known(v_fst_2246_, 1);
v___x_2265_ = lean_unbox(v_val_2264_);
lean_dec(v_val_2264_);
v_a_2143_ = v___x_2265_;
goto v___jp_2142_;
}
}
}
else
{
lean_object* v_a_2268_; 
lean_dec(v_fst_2198_);
lean_dec(v_fst_2197_);
lean_dec(v_a_2141_);
v_a_2268_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2244_, 1);
v_a_2101_ = v_a_2268_;
goto v___jp_2100_;
}
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2222_ == 0)
{
v___x_2275_ = v___x_2221_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 0, v_foApprox_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 1, v_ctxApprox_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 2, v_quasiPatternApprox_2203_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 3, v_constApprox_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 4, v_isDefEqStuckEx_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 6, v_proofIrrelevance_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 7, v_assignSyntheticOpaque_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 8, v_offsetCnstrs_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 9, v_transparency_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 10, v_etaStruct_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 11, v_univApprox_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 12, v_iota_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 13, v_beta_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 14, v_proj_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 15, v_zeta_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 16, v_zetaDelta_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 17, v_zetaUnused_2217_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 18, v_zetaHave_2218_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, 19, v_canUnfoldPredicateConfig_2219_);
v___x_2275_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
uint64_t v___x_2276_; lean_object* v_cls_2277_; lean_object* v___y_2279_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_ctor_set_uint8(v___x_2275_, 5, v___x_2190_);
v___x_2276_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2275_);
v_cls_2277_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2299_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2299_, 0, v___x_2275_);
lean_ctor_set_uint64(v___x_2299_, sizeof(void*)*1, v___x_2276_);
lean_inc(v_customCanUnfoldPredicate_x3f_2231_);
lean_inc(v_synthPendingDepth_2230_);
lean_inc(v_defEqCtx_x3f_2229_);
lean_inc_ref(v_localInstances_2228_);
lean_inc_ref(v_lctx_2227_);
lean_inc(v_zetaDeltaSet_2226_);
v___x_2300_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v_zetaDeltaSet_2226_);
lean_ctor_set(v___x_2300_, 2, v_lctx_2227_);
lean_ctor_set(v___x_2300_, 3, v_localInstances_2228_);
lean_ctor_set(v___x_2300_, 4, v_defEqCtx_x3f_2229_);
lean_ctor_set(v___x_2300_, 5, v_synthPendingDepth_2230_);
lean_ctor_set(v___x_2300_, 6, v_customCanUnfoldPredicate_x3f_2231_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*7, v_trackZetaDelta_2225_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*7 + 1, v_univApprox_2232_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2233_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*7 + 3, v_cacheInferType_2234_);
v___x_2301_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_lhs_2269_, v_t_2064_, v___x_2300_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; uint8_t v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
v___x_2303_ = lean_unbox(v_a_2302_);
lean_dec(v_a_2302_);
if (v___x_2303_ == 0)
{
lean_dec_ref_known(v___x_2300_, 7);
lean_dec_ref(v_rhs_2270_);
lean_dec_ref(v_s_2065_);
v___y_2279_ = v___x_2301_;
goto v___jp_2278_;
}
else
{
lean_object* v___x_2304_; 
lean_dec_ref_known(v___x_2301_, 1);
v___x_2304_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_rhs_2270_, v_s_2065_, v___x_2300_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec_ref_known(v___x_2300_, 7);
v___y_2279_ = v___x_2304_;
goto v___jp_2278_;
}
}
else
{
lean_dec_ref_known(v___x_2300_, 7);
lean_dec_ref(v_rhs_2270_);
lean_dec_ref(v_s_2065_);
v___y_2279_ = v___x_2301_;
goto v___jp_2278_;
}
v___jp_2278_:
{
if (lean_obj_tag(v___y_2279_) == 0)
{
lean_object* v_a_2280_; uint8_t v___x_2281_; 
v_a_2280_ = lean_ctor_get(v___y_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___y_2279_, 1);
v___x_2281_ = lean_unbox(v_a_2280_);
if (v___x_2281_ == 0)
{
lean_dec(v_a_2280_);
lean_del_object(v___x_2272_);
lean_dec(v_constraints_2236_);
lean_dec(v_fst_2198_);
lean_dec(v_fst_2197_);
lean_dec(v_a_2141_);
lean_dec(v_candidate_2063_);
v_a_2105_ = v___x_2190_;
goto v___jp_2104_;
}
else
{
lean_object* v_options_2282_; uint8_t v_hasTrace_2283_; 
v_options_2282_ = lean_ctor_get(v_a_2069_, 1);
v_hasTrace_2283_ = lean_ctor_get_uint8(v_options_2282_, sizeof(void*)*1);
if (v_hasTrace_2283_ == 0)
{
uint8_t v___x_2284_; 
lean_del_object(v___x_2272_);
lean_dec(v_candidate_2063_);
v___x_2284_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
v___y_2238_ = v___x_2284_;
v___y_2239_ = v_a_2067_;
v___y_2240_ = v_a_2068_;
v___y_2241_ = v_a_2069_;
v___y_2242_ = v_a_2070_;
goto v___jp_2237_;
}
else
{
lean_object* v_toCold_2285_; lean_object* v_inheritedTraceOptions_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_toCold_2285_ = lean_ctor_get(v_a_2069_, 0);
v_inheritedTraceOptions_2286_ = lean_ctor_get(v_toCold_2285_, 4);
v___x_2287_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2288_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2286_, v_options_2282_, v___x_2287_);
if (v___x_2288_ == 0)
{
uint8_t v___x_2289_; 
lean_del_object(v___x_2272_);
lean_dec(v_candidate_2063_);
v___x_2289_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
v___y_2238_ = v___x_2289_;
v___y_2239_ = v_a_2067_;
v___y_2240_ = v_a_2068_;
v___y_2241_ = v_a_2069_;
v___y_2242_ = v_a_2070_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2290_ = l_Lean_MessageData_ofName(v_candidate_2063_);
v___x_2291_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10);
if (v_isShared_2273_ == 0)
{
lean_ctor_set_tag(v___x_2272_, 7);
lean_ctor_set(v___x_2272_, 1, v___x_2291_);
lean_ctor_set(v___x_2272_, 0, v___x_2290_);
v___x_2293_ = v___x_2272_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2277_, v___x_2293_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2294_) == 0)
{
uint8_t v___x_2295_; 
lean_dec_ref_known(v___x_2294_, 1);
v___x_2295_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
v___y_2238_ = v___x_2295_;
v___y_2239_ = v_a_2067_;
v___y_2240_ = v_a_2068_;
v___y_2241_ = v_a_2069_;
v___y_2242_ = v_a_2070_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2296_; 
lean_dec(v_a_2280_);
lean_dec(v_constraints_2236_);
lean_dec(v_fst_2198_);
lean_dec(v_fst_2197_);
lean_dec(v_a_2141_);
v_a_2296_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2294_, 1);
v_a_2101_ = v_a_2296_;
goto v___jp_2100_;
}
}
}
}
}
}
else
{
lean_object* v_a_2298_; 
lean_del_object(v___x_2272_);
lean_dec(v_constraints_2236_);
lean_dec(v_fst_2198_);
lean_dec(v_fst_2197_);
lean_dec(v_a_2141_);
lean_dec(v_candidate_2063_);
v_a_2298_ = lean_ctor_get(v___y_2279_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___y_2279_, 1);
v_a_2101_ = v_a_2298_;
goto v___jp_2100_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2308_; 
lean_dec(v_a_2141_);
lean_dec_ref(v_s_2065_);
lean_dec_ref(v_t_2064_);
lean_dec(v_candidate_2063_);
v_a_2308_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2194_, 1);
v_a_2101_ = v_a_2308_;
goto v___jp_2100_;
}
}
else
{
lean_object* v_a_2309_; 
lean_dec(v_a_2141_);
lean_dec_ref(v_s_2065_);
lean_dec_ref(v_t_2064_);
lean_dec(v_candidate_2063_);
v_a_2309_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2191_, 1);
v_a_2101_ = v_a_2309_;
goto v___jp_2100_;
}
}
else
{
lean_object* v_a_2310_; 
lean_dec(v_a_2185_);
lean_dec(v_a_2141_);
lean_dec_ref(v_s_2065_);
lean_dec_ref(v_t_2064_);
lean_dec(v_candidate_2063_);
v_a_2310_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2188_, 1);
v_a_2101_ = v_a_2310_;
goto v___jp_2100_;
}
}
else
{
lean_object* v_a_2311_; 
lean_dec(v_a_2141_);
lean_dec_ref(v_s_2065_);
lean_dec_ref(v_t_2064_);
lean_dec(v_candidate_2063_);
v_a_2311_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2184_, 1);
v_a_2101_ = v_a_2311_;
goto v___jp_2100_;
}
v___jp_2142_:
{
if (v_a_2143_ == 0)
{
lean_dec(v_a_2141_);
v_a_2105_ = v_a_2143_;
goto v___jp_2104_;
}
else
{
uint8_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = 0;
v___x_2145_ = l_Lean_Meta_processPostponed(v_mayPostpone_2066_, v___x_2144_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2182_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2182_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2182_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_unbox(v_a_2146_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_del_object(v___x_2148_);
lean_dec(v_a_2146_);
lean_dec(v_a_2141_);
v___x_2151_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2073_, v_a_2068_, v_a_2070_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2159_; 
lean_del_object(v___x_2075_);
lean_dec(v_a_2073_);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v___x_2151_, 0);
lean_dec(v_unused_2160_);
v___x_2153_ = v___x_2151_;
v_isShared_2154_ = v_isSharedCheck_2159_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v___x_2151_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2159_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2155_ = lean_box(v___x_2144_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2155_);
v___x_2157_ = v___x_2153_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
else
{
lean_object* v_a_2161_; 
v_a_2161_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2151_, 1);
v_a_2101_ = v_a_2161_;
goto v___jp_2100_;
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v_postponed_2164_; lean_object* v_mctx_2165_; lean_object* v_cache_2166_; lean_object* v_zetaDeltaFVarIds_2167_; lean_object* v_diag_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2180_; 
lean_del_object(v___x_2075_);
lean_dec(v_a_2073_);
v___x_2162_ = lean_st_ref_get(v_a_2068_);
v___x_2163_ = lean_st_ref_take(v_a_2068_);
v_postponed_2164_ = lean_ctor_get(v___x_2162_, 3);
lean_inc_ref(v_postponed_2164_);
lean_dec(v___x_2162_);
v_mctx_2165_ = lean_ctor_get(v___x_2163_, 0);
v_cache_2166_ = lean_ctor_get(v___x_2163_, 1);
v_zetaDeltaFVarIds_2167_ = lean_ctor_get(v___x_2163_, 2);
v_diag_2168_ = lean_ctor_get(v___x_2163_, 4);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v___x_2163_, 3);
lean_dec(v_unused_2181_);
v___x_2170_ = v___x_2163_;
v_isShared_2171_ = v_isSharedCheck_2180_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_diag_2168_);
lean_inc(v_zetaDeltaFVarIds_2167_);
lean_inc(v_cache_2166_);
lean_inc(v_mctx_2165_);
lean_dec(v___x_2163_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2180_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = l_Lean_PersistentArray_append___redArg(v_a_2141_, v_postponed_2164_);
lean_dec_ref(v_postponed_2164_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 3, v___x_2172_);
v___x_2174_ = v___x_2170_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_mctx_2165_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_cache_2166_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_zetaDeltaFVarIds_2167_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2179_, 4, v_diag_2168_);
v___x_2174_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2175_ = lean_st_ref_put(v_a_2068_, v___x_2174_);
if (v_isShared_2149_ == 0)
{
v___x_2177_ = v___x_2148_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2146_);
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
}
}
else
{
lean_object* v_a_2183_; 
lean_dec(v_a_2141_);
v_a_2183_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2145_, 1);
v_a_2101_ = v_a_2183_;
goto v___jp_2100_;
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_del_object(v___x_2075_);
lean_dec(v_a_2073_);
lean_dec_ref(v_s_2065_);
lean_dec_ref(v_t_2064_);
lean_dec(v_candidate_2063_);
v_a_2312_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2140_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2140_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
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
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v_s_2065_);
lean_dec_ref(v_t_2064_);
lean_dec(v_candidate_2063_);
v_a_2326_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2072_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2072_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(lean_object* v_candidate_2334_, lean_object* v_t_2335_, lean_object* v_s_2336_, lean_object* v_mayPostpone_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
uint8_t v_mayPostpone_boxed_2343_; lean_object* v_res_2344_; 
v_mayPostpone_boxed_2343_ = lean_unbox(v_mayPostpone_2337_);
v_res_2344_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2334_, v_t_2335_, v_s_2336_, v_mayPostpone_boxed_2343_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
return v_res_2344_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = lean_unsigned_to_nat(32u);
v___x_2346_ = lean_mk_empty_array_with_capacity(v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2348_ = ((size_t)5ULL);
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = lean_unsigned_to_nat(32u);
v___x_2351_ = lean_mk_empty_array_with_capacity(v___x_2350_);
v___x_2352_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0);
v___x_2353_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v___x_2351_);
lean_ctor_set(v___x_2353_, 2, v___x_2349_);
lean_ctor_set(v___x_2353_, 3, v___x_2349_);
lean_ctor_set_usize(v___x_2353_, 4, v___x_2348_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v_traceState_2357_; lean_object* v_traces_2358_; lean_object* v___x_2359_; lean_object* v_traceState_2360_; lean_object* v_env_2361_; lean_object* v_nextMacroScope_2362_; lean_object* v_ngen_2363_; lean_object* v_auxDeclNGen_2364_; lean_object* v_cache_2365_; lean_object* v_messages_2366_; lean_object* v_infoState_2367_; lean_object* v_snapshotTasks_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2387_; 
v___x_2356_ = lean_st_ref_get(v___y_2354_);
v_traceState_2357_ = lean_ctor_get(v___x_2356_, 4);
lean_inc_ref(v_traceState_2357_);
lean_dec(v___x_2356_);
v_traces_2358_ = lean_ctor_get(v_traceState_2357_, 0);
lean_inc_ref(v_traces_2358_);
lean_dec_ref(v_traceState_2357_);
v___x_2359_ = lean_st_ref_take(v___y_2354_);
v_traceState_2360_ = lean_ctor_get(v___x_2359_, 4);
v_env_2361_ = lean_ctor_get(v___x_2359_, 0);
v_nextMacroScope_2362_ = lean_ctor_get(v___x_2359_, 1);
v_ngen_2363_ = lean_ctor_get(v___x_2359_, 2);
v_auxDeclNGen_2364_ = lean_ctor_get(v___x_2359_, 3);
v_cache_2365_ = lean_ctor_get(v___x_2359_, 5);
v_messages_2366_ = lean_ctor_get(v___x_2359_, 6);
v_infoState_2367_ = lean_ctor_get(v___x_2359_, 7);
v_snapshotTasks_2368_ = lean_ctor_get(v___x_2359_, 8);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2370_ = v___x_2359_;
v_isShared_2371_ = v_isSharedCheck_2387_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_snapshotTasks_2368_);
lean_inc(v_infoState_2367_);
lean_inc(v_messages_2366_);
lean_inc(v_cache_2365_);
lean_inc(v_traceState_2360_);
lean_inc(v_auxDeclNGen_2364_);
lean_inc(v_ngen_2363_);
lean_inc(v_nextMacroScope_2362_);
lean_inc(v_env_2361_);
lean_dec(v___x_2359_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2387_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
uint64_t v_tid_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2385_; 
v_tid_2372_ = lean_ctor_get_uint64(v_traceState_2360_, sizeof(void*)*1);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_traceState_2360_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v_traceState_2360_, 0);
lean_dec(v_unused_2386_);
v___x_2374_ = v_traceState_2360_;
v_isShared_2375_ = v_isSharedCheck_2385_;
goto v_resetjp_2373_;
}
else
{
lean_dec(v_traceState_2360_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2385_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2376_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2376_);
v___x_2378_ = v___x_2374_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2376_);
lean_ctor_set_uint64(v_reuseFailAlloc_2384_, sizeof(void*)*1, v_tid_2372_);
v___x_2378_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2380_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 4, v___x_2378_);
v___x_2380_ = v___x_2370_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_env_2361_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_nextMacroScope_2362_);
lean_ctor_set(v_reuseFailAlloc_2383_, 2, v_ngen_2363_);
lean_ctor_set(v_reuseFailAlloc_2383_, 3, v_auxDeclNGen_2364_);
lean_ctor_set(v_reuseFailAlloc_2383_, 4, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2383_, 5, v_cache_2365_);
lean_ctor_set(v_reuseFailAlloc_2383_, 6, v_messages_2366_);
lean_ctor_set(v_reuseFailAlloc_2383_, 7, v_infoState_2367_);
lean_ctor_set(v_reuseFailAlloc_2383_, 8, v_snapshotTasks_2368_);
v___x_2380_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_st_ref_put(v___y_2354_, v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_traces_2358_);
return v___x_2382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___boxed(lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2388_);
lean_dec(v___y_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v_res_2402_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(lean_object* v_opts_2403_, lean_object* v_opt_2404_){
_start:
{
lean_object* v_name_2405_; lean_object* v_defValue_2406_; lean_object* v_map_2407_; lean_object* v___x_2408_; 
v_name_2405_ = lean_ctor_get(v_opt_2404_, 0);
v_defValue_2406_ = lean_ctor_get(v_opt_2404_, 1);
v_map_2407_ = lean_ctor_get(v_opts_2403_, 0);
v___x_2408_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2407_, v_name_2405_);
if (lean_obj_tag(v___x_2408_) == 0)
{
uint8_t v___x_2409_; 
v___x_2409_ = lean_unbox(v_defValue_2406_);
return v___x_2409_;
}
else
{
lean_object* v_val_2410_; 
v_val_2410_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_val_2410_);
lean_dec_ref_known(v___x_2408_, 1);
if (lean_obj_tag(v_val_2410_) == 1)
{
uint8_t v_v_2411_; 
v_v_2411_ = lean_ctor_get_uint8(v_val_2410_, 0);
lean_dec_ref_known(v_val_2410_, 0);
return v_v_2411_;
}
else
{
uint8_t v___x_2412_; 
lean_dec(v_val_2410_);
v___x_2412_ = lean_unbox(v_defValue_2406_);
return v___x_2412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(lean_object* v_opts_2413_, lean_object* v_opt_2414_){
_start:
{
uint8_t v_res_2415_; lean_object* v_r_2416_; 
v_res_2415_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2413_, v_opt_2414_);
lean_dec_ref(v_opt_2414_);
lean_dec_ref(v_opts_2413_);
v_r_2416_ = lean_box(v_res_2415_);
return v_r_2416_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4));
v___x_2425_ = l_Lean_stringToMessageData(v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object* v_candidate_2426_, lean_object* v_t_2427_, lean_object* v_s_2428_, lean_object* v_x_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2435_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1);
v___x_2436_ = l_Lean_MessageData_ofName(v_candidate_2426_);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = l_Lean_MessageData_ofExpr(v_t_2427_);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = l_Lean_MessageData_ofExpr(v_s_2428_);
v___x_2445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object* v_candidate_2447_, lean_object* v_t_2448_, lean_object* v_s_2449_, lean_object* v_x_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(v_candidate_2447_, v_t_2448_, v_s_2449_, v_x_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec_ref(v_x_2450_);
return v_res_2456_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(lean_object* v_e_2457_){
_start:
{
if (lean_obj_tag(v_e_2457_) == 0)
{
uint8_t v___x_2458_; 
v___x_2458_ = 2;
return v___x_2458_;
}
else
{
lean_object* v_a_2459_; uint8_t v___x_2460_; 
v_a_2459_ = lean_ctor_get(v_e_2457_, 0);
v___x_2460_ = lean_unbox(v_a_2459_);
if (v___x_2460_ == 0)
{
uint8_t v___x_2461_; 
v___x_2461_ = 1;
return v___x_2461_;
}
else
{
uint8_t v___x_2462_; 
v___x_2462_ = 0;
return v___x_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(lean_object* v_e_2463_){
_start:
{
uint8_t v_res_2464_; lean_object* v_r_2465_; 
v_res_2464_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_e_2463_);
lean_dec_ref(v_e_2463_);
v_r_2465_ = lean_box(v_res_2464_);
return v_r_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(size_t v_sz_2466_, size_t v_i_2467_, lean_object* v_bs_2468_){
_start:
{
uint8_t v___x_2469_; 
v___x_2469_ = lean_usize_dec_lt(v_i_2467_, v_sz_2466_);
if (v___x_2469_ == 0)
{
return v_bs_2468_;
}
else
{
lean_object* v_v_2470_; lean_object* v_msg_2471_; lean_object* v___x_2472_; lean_object* v_bs_x27_2473_; size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v_v_2470_ = lean_array_uget_borrowed(v_bs_2468_, v_i_2467_);
v_msg_2471_ = lean_ctor_get(v_v_2470_, 1);
lean_inc_ref(v_msg_2471_);
v___x_2472_ = lean_unsigned_to_nat(0u);
v_bs_x27_2473_ = lean_array_uset(v_bs_2468_, v_i_2467_, v___x_2472_);
v___x_2474_ = ((size_t)1ULL);
v___x_2475_ = lean_usize_add(v_i_2467_, v___x_2474_);
v___x_2476_ = lean_array_uset(v_bs_x27_2473_, v_i_2467_, v_msg_2471_);
v_i_2467_ = v___x_2475_;
v_bs_2468_ = v___x_2476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8___boxed(lean_object* v_sz_2478_, lean_object* v_i_2479_, lean_object* v_bs_2480_){
_start:
{
size_t v_sz_boxed_2481_; size_t v_i_boxed_2482_; lean_object* v_res_2483_; 
v_sz_boxed_2481_ = lean_unbox_usize(v_sz_2478_);
lean_dec(v_sz_2478_);
v_i_boxed_2482_ = lean_unbox_usize(v_i_2479_);
lean_dec(v_i_2479_);
v_res_2483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(v_sz_boxed_2481_, v_i_boxed_2482_, v_bs_2480_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(lean_object* v_oldTraces_2484_, lean_object* v_data_2485_, lean_object* v_ref_2486_, lean_object* v_msg_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_toCold_2493_; lean_object* v_options_2494_; lean_object* v_currRecDepth_2495_; lean_object* v_maxRecDepth_2496_; lean_object* v_ref_2497_; lean_object* v_currNamespace_2498_; lean_object* v_openDecls_2499_; lean_object* v_initHeartbeats_2500_; lean_object* v_maxHeartbeats_2501_; lean_object* v_currMacroScope_2502_; uint8_t v_diag_2503_; uint8_t v_suppressElabErrors_2504_; lean_object* v___x_2505_; lean_object* v_traceState_2506_; lean_object* v_traces_2507_; lean_object* v_ref_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; size_t v_sz_2511_; size_t v___x_2512_; lean_object* v___x_2513_; lean_object* v_msg_2514_; lean_object* v___x_2515_; lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2553_; 
v_toCold_2493_ = lean_ctor_get(v___y_2490_, 0);
v_options_2494_ = lean_ctor_get(v___y_2490_, 1);
v_currRecDepth_2495_ = lean_ctor_get(v___y_2490_, 2);
v_maxRecDepth_2496_ = lean_ctor_get(v___y_2490_, 3);
v_ref_2497_ = lean_ctor_get(v___y_2490_, 4);
v_currNamespace_2498_ = lean_ctor_get(v___y_2490_, 5);
v_openDecls_2499_ = lean_ctor_get(v___y_2490_, 6);
v_initHeartbeats_2500_ = lean_ctor_get(v___y_2490_, 7);
v_maxHeartbeats_2501_ = lean_ctor_get(v___y_2490_, 8);
v_currMacroScope_2502_ = lean_ctor_get(v___y_2490_, 9);
v_diag_2503_ = lean_ctor_get_uint8(v___y_2490_, sizeof(void*)*10);
v_suppressElabErrors_2504_ = lean_ctor_get_uint8(v___y_2490_, sizeof(void*)*10 + 1);
v___x_2505_ = lean_st_ref_get(v___y_2491_);
v_traceState_2506_ = lean_ctor_get(v___x_2505_, 4);
lean_inc_ref(v_traceState_2506_);
lean_dec(v___x_2505_);
v_traces_2507_ = lean_ctor_get(v_traceState_2506_, 0);
lean_inc_ref(v_traces_2507_);
lean_dec_ref(v_traceState_2506_);
v_ref_2508_ = l_Lean_replaceRef(v_ref_2486_, v_ref_2497_);
lean_inc(v_currMacroScope_2502_);
lean_inc(v_maxHeartbeats_2501_);
lean_inc(v_initHeartbeats_2500_);
lean_inc(v_openDecls_2499_);
lean_inc(v_currNamespace_2498_);
lean_inc(v_maxRecDepth_2496_);
lean_inc(v_currRecDepth_2495_);
lean_inc_ref(v_options_2494_);
lean_inc_ref(v_toCold_2493_);
v___x_2509_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2509_, 0, v_toCold_2493_);
lean_ctor_set(v___x_2509_, 1, v_options_2494_);
lean_ctor_set(v___x_2509_, 2, v_currRecDepth_2495_);
lean_ctor_set(v___x_2509_, 3, v_maxRecDepth_2496_);
lean_ctor_set(v___x_2509_, 4, v_ref_2508_);
lean_ctor_set(v___x_2509_, 5, v_currNamespace_2498_);
lean_ctor_set(v___x_2509_, 6, v_openDecls_2499_);
lean_ctor_set(v___x_2509_, 7, v_initHeartbeats_2500_);
lean_ctor_set(v___x_2509_, 8, v_maxHeartbeats_2501_);
lean_ctor_set(v___x_2509_, 9, v_currMacroScope_2502_);
lean_ctor_set_uint8(v___x_2509_, sizeof(void*)*10, v_diag_2503_);
lean_ctor_set_uint8(v___x_2509_, sizeof(void*)*10 + 1, v_suppressElabErrors_2504_);
v___x_2510_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2507_);
lean_dec_ref(v_traces_2507_);
v_sz_2511_ = lean_array_size(v___x_2510_);
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7_spec__8(v_sz_2511_, v___x_2512_, v___x_2510_);
v_msg_2514_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2514_, 0, v_data_2485_);
lean_ctor_set(v_msg_2514_, 1, v_msg_2487_);
lean_ctor_set(v_msg_2514_, 2, v___x_2513_);
v___x_2515_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_2514_, v___y_2488_, v___y_2489_, v___x_2509_, v___y_2491_);
lean_dec_ref_known(v___x_2509_, 10);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2553_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2553_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v_traceState_2521_; lean_object* v_env_2522_; lean_object* v_nextMacroScope_2523_; lean_object* v_ngen_2524_; lean_object* v_auxDeclNGen_2525_; lean_object* v_cache_2526_; lean_object* v_messages_2527_; lean_object* v_infoState_2528_; lean_object* v_snapshotTasks_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2552_; 
v___x_2520_ = lean_st_ref_take(v___y_2491_);
v_traceState_2521_ = lean_ctor_get(v___x_2520_, 4);
v_env_2522_ = lean_ctor_get(v___x_2520_, 0);
v_nextMacroScope_2523_ = lean_ctor_get(v___x_2520_, 1);
v_ngen_2524_ = lean_ctor_get(v___x_2520_, 2);
v_auxDeclNGen_2525_ = lean_ctor_get(v___x_2520_, 3);
v_cache_2526_ = lean_ctor_get(v___x_2520_, 5);
v_messages_2527_ = lean_ctor_get(v___x_2520_, 6);
v_infoState_2528_ = lean_ctor_get(v___x_2520_, 7);
v_snapshotTasks_2529_ = lean_ctor_get(v___x_2520_, 8);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2531_ = v___x_2520_;
v_isShared_2532_ = v_isSharedCheck_2552_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_snapshotTasks_2529_);
lean_inc(v_infoState_2528_);
lean_inc(v_messages_2527_);
lean_inc(v_cache_2526_);
lean_inc(v_traceState_2521_);
lean_inc(v_auxDeclNGen_2525_);
lean_inc(v_ngen_2524_);
lean_inc(v_nextMacroScope_2523_);
lean_inc(v_env_2522_);
lean_dec(v___x_2520_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2552_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
uint64_t v_tid_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2550_; 
v_tid_2533_ = lean_ctor_get_uint64(v_traceState_2521_, sizeof(void*)*1);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_traceState_2521_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v_traceState_2521_, 0);
lean_dec(v_unused_2551_);
v___x_2535_ = v_traceState_2521_;
v_isShared_2536_ = v_isSharedCheck_2550_;
goto v_resetjp_2534_;
}
else
{
lean_dec(v_traceState_2521_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2550_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v_ref_2486_);
lean_ctor_set(v___x_2537_, 1, v_a_2516_);
v___x_2538_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2484_, v___x_2537_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2538_);
v___x_2540_ = v___x_2535_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2538_);
lean_ctor_set_uint64(v_reuseFailAlloc_2549_, sizeof(void*)*1, v_tid_2533_);
v___x_2540_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2542_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 4, v___x_2540_);
v___x_2542_ = v___x_2531_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_env_2522_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_nextMacroScope_2523_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_ngen_2524_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_auxDeclNGen_2525_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2548_, 5, v_cache_2526_);
lean_ctor_set(v_reuseFailAlloc_2548_, 6, v_messages_2527_);
lean_ctor_set(v_reuseFailAlloc_2548_, 7, v_infoState_2528_);
lean_ctor_set(v_reuseFailAlloc_2548_, 8, v_snapshotTasks_2529_);
v___x_2542_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2543_ = lean_st_ref_put(v___y_2491_, v___x_2542_);
v___x_2544_ = lean_box(0);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2544_);
v___x_2546_ = v___x_2518_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(lean_object* v_oldTraces_2554_, lean_object* v_data_2555_, lean_object* v_ref_2556_, lean_object* v_msg_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_oldTraces_2554_, v_data_2555_, v_ref_2556_, v_msg_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(lean_object* v_opts_2564_, lean_object* v_opt_2565_){
_start:
{
lean_object* v_name_2566_; lean_object* v_defValue_2567_; lean_object* v_map_2568_; lean_object* v___x_2569_; 
v_name_2566_ = lean_ctor_get(v_opt_2565_, 0);
v_defValue_2567_ = lean_ctor_get(v_opt_2565_, 1);
v_map_2568_ = lean_ctor_get(v_opts_2564_, 0);
v___x_2569_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2568_, v_name_2566_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_inc(v_defValue_2567_);
return v_defValue_2567_;
}
else
{
lean_object* v_val_2570_; 
v_val_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_val_2570_);
lean_dec_ref_known(v___x_2569_, 1);
if (lean_obj_tag(v_val_2570_) == 3)
{
lean_object* v_v_2571_; 
v_v_2571_ = lean_ctor_get(v_val_2570_, 0);
lean_inc(v_v_2571_);
lean_dec_ref_known(v_val_2570_, 1);
return v_v_2571_;
}
else
{
lean_dec(v_val_2570_);
lean_inc(v_defValue_2567_);
return v_defValue_2567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(lean_object* v_opts_2572_, lean_object* v_opt_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2572_, v_opt_2573_);
lean_dec_ref(v_opt_2573_);
lean_dec_ref(v_opts_2572_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(lean_object* v_x_2575_){
_start:
{
if (lean_obj_tag(v_x_2575_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v_a_2577_ = lean_ctor_get(v_x_2575_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_x_2575_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v_x_2575_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v_x_2575_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 1);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v_x_2575_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_x_2575_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v_x_2575_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v_x_2575_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 0);
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg___boxed(lean_object* v_x_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_x_2593_);
return v_res_2595_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0));
v___x_2598_ = l_Lean_stringToMessageData(v___x_2597_);
return v___x_2598_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2(void){
_start:
{
lean_object* v___x_2599_; double v___x_2600_; 
v___x_2599_ = lean_unsigned_to_nat(1000u);
v___x_2600_ = lean_float_of_nat(v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(lean_object* v_cls_2601_, uint8_t v_collapsed_2602_, lean_object* v_tag_2603_, lean_object* v_opts_2604_, uint8_t v_clsEnabled_2605_, lean_object* v_oldTraces_2606_, lean_object* v_msg_2607_, lean_object* v_resStartStop_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_fst_2614_; lean_object* v_snd_2615_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v_data_2619_; lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; lean_object* v___y_2635_; lean_object* v_a_2636_; uint8_t v___y_2651_; double v___y_2682_; 
v_fst_2614_ = lean_ctor_get(v_resStartStop_2608_, 0);
lean_inc(v_fst_2614_);
v_snd_2615_ = lean_ctor_get(v_resStartStop_2608_, 1);
lean_inc(v_snd_2615_);
lean_dec_ref(v_resStartStop_2608_);
v_fst_2630_ = lean_ctor_get(v_snd_2615_, 0);
lean_inc(v_fst_2630_);
v_snd_2631_ = lean_ctor_get(v_snd_2615_, 1);
lean_inc(v_snd_2631_);
lean_dec(v_snd_2615_);
v___x_2632_ = l_Lean_trace_profiler;
v___x_2633_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2604_, v___x_2632_);
if (v___x_2633_ == 0)
{
v___y_2651_ = v___x_2633_;
goto v___jp_2650_;
}
else
{
lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2688_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_2604_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2690_; double v___x_2691_; double v___x_2692_; double v___x_2693_; 
v___x_2689_ = l_Lean_trace_profiler_threshold;
v___x_2690_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2604_, v___x_2689_);
v___x_2691_ = lean_float_of_nat(v___x_2690_);
v___x_2692_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2);
v___x_2693_ = lean_float_div(v___x_2691_, v___x_2692_);
v___y_2682_ = v___x_2693_;
goto v___jp_2681_;
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; double v___x_2696_; 
v___x_2694_ = l_Lean_trace_profiler_threshold;
v___x_2695_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_2604_, v___x_2694_);
v___x_2696_ = lean_float_of_nat(v___x_2695_);
v___y_2682_ = v___x_2696_;
goto v___jp_2681_;
}
}
v___jp_2616_:
{
lean_object* v___x_2620_; 
lean_inc(v___y_2617_);
v___x_2620_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_oldTraces_2606_, v_data_2619_, v___y_2617_, v___y_2618_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v___x_2621_; 
lean_dec_ref_known(v___x_2620_, 1);
v___x_2621_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_fst_2614_);
return v___x_2621_;
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_fst_2614_);
v_a_2622_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2620_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2620_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
v___jp_2634_:
{
uint8_t v_result_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; double v___x_2640_; lean_object* v_data_2641_; 
v_result_2637_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_fst_2614_);
v___x_2638_ = lean_box(v_result_2637_);
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
v___x_2640_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
lean_inc_ref(v_tag_2603_);
lean_inc_ref(v___x_2639_);
lean_inc(v_cls_2601_);
v_data_2641_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2641_, 0, v_cls_2601_);
lean_ctor_set(v_data_2641_, 1, v___x_2639_);
lean_ctor_set(v_data_2641_, 2, v_tag_2603_);
lean_ctor_set_float(v_data_2641_, sizeof(void*)*3, v___x_2640_);
lean_ctor_set_float(v_data_2641_, sizeof(void*)*3 + 8, v___x_2640_);
lean_ctor_set_uint8(v_data_2641_, sizeof(void*)*3 + 16, v_collapsed_2602_);
if (v___x_2633_ == 0)
{
lean_dec_ref_known(v___x_2639_, 1);
lean_dec(v_snd_2631_);
lean_dec(v_fst_2630_);
lean_dec_ref(v_tag_2603_);
lean_dec(v_cls_2601_);
v___y_2617_ = v___y_2635_;
v___y_2618_ = v_a_2636_;
v_data_2619_ = v_data_2641_;
goto v___jp_2616_;
}
else
{
lean_object* v_data_2642_; double v___x_2643_; double v___x_2644_; 
lean_dec_ref_known(v_data_2641_, 3);
v_data_2642_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2642_, 0, v_cls_2601_);
lean_ctor_set(v_data_2642_, 1, v___x_2639_);
lean_ctor_set(v_data_2642_, 2, v_tag_2603_);
v___x_2643_ = lean_unbox_float(v_fst_2630_);
lean_dec(v_fst_2630_);
lean_ctor_set_float(v_data_2642_, sizeof(void*)*3, v___x_2643_);
v___x_2644_ = lean_unbox_float(v_snd_2631_);
lean_dec(v_snd_2631_);
lean_ctor_set_float(v_data_2642_, sizeof(void*)*3 + 8, v___x_2644_);
lean_ctor_set_uint8(v_data_2642_, sizeof(void*)*3 + 16, v_collapsed_2602_);
v___y_2617_ = v___y_2635_;
v___y_2618_ = v_a_2636_;
v_data_2619_ = v_data_2642_;
goto v___jp_2616_;
}
}
v___jp_2645_:
{
lean_object* v_ref_2646_; lean_object* v___x_2647_; 
v_ref_2646_ = lean_ctor_get(v___y_2611_, 4);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
lean_inc(v___y_2610_);
lean_inc_ref(v___y_2609_);
lean_inc(v_fst_2614_);
v___x_2647_ = lean_apply_6(v_msg_2607_, v_fst_2614_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, lean_box(0));
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___y_2635_ = v_ref_2646_;
v_a_2636_ = v_a_2648_;
goto v___jp_2634_;
}
else
{
lean_object* v___x_2649_; 
lean_dec_ref_known(v___x_2647_, 1);
v___x_2649_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1);
v___y_2635_ = v_ref_2646_;
v_a_2636_ = v___x_2649_;
goto v___jp_2634_;
}
}
v___jp_2650_:
{
if (v_clsEnabled_2605_ == 0)
{
if (v___y_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v_traceState_2653_; lean_object* v_env_2654_; lean_object* v_nextMacroScope_2655_; lean_object* v_ngen_2656_; lean_object* v_auxDeclNGen_2657_; lean_object* v_cache_2658_; lean_object* v_messages_2659_; lean_object* v_infoState_2660_; lean_object* v_snapshotTasks_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_snd_2631_);
lean_dec(v_fst_2630_);
lean_dec_ref(v_msg_2607_);
lean_dec_ref(v_tag_2603_);
lean_dec(v_cls_2601_);
v___x_2652_ = lean_st_ref_take(v___y_2612_);
v_traceState_2653_ = lean_ctor_get(v___x_2652_, 4);
v_env_2654_ = lean_ctor_get(v___x_2652_, 0);
v_nextMacroScope_2655_ = lean_ctor_get(v___x_2652_, 1);
v_ngen_2656_ = lean_ctor_get(v___x_2652_, 2);
v_auxDeclNGen_2657_ = lean_ctor_get(v___x_2652_, 3);
v_cache_2658_ = lean_ctor_get(v___x_2652_, 5);
v_messages_2659_ = lean_ctor_get(v___x_2652_, 6);
v_infoState_2660_ = lean_ctor_get(v___x_2652_, 7);
v_snapshotTasks_2661_ = lean_ctor_get(v___x_2652_, 8);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2663_ = v___x_2652_;
v_isShared_2664_ = v_isSharedCheck_2680_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_snapshotTasks_2661_);
lean_inc(v_infoState_2660_);
lean_inc(v_messages_2659_);
lean_inc(v_cache_2658_);
lean_inc(v_traceState_2653_);
lean_inc(v_auxDeclNGen_2657_);
lean_inc(v_ngen_2656_);
lean_inc(v_nextMacroScope_2655_);
lean_inc(v_env_2654_);
lean_dec(v___x_2652_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2680_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
uint64_t v_tid_2665_; lean_object* v_traces_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2679_; 
v_tid_2665_ = lean_ctor_get_uint64(v_traceState_2653_, sizeof(void*)*1);
v_traces_2666_ = lean_ctor_get(v_traceState_2653_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_traceState_2653_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2668_ = v_traceState_2653_;
v_isShared_2669_ = v_isSharedCheck_2679_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_traces_2666_);
lean_dec(v_traceState_2653_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2679_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2670_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2606_, v_traces_2666_);
lean_dec_ref(v_traces_2666_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2670_);
v___x_2672_ = v___x_2668_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2670_);
lean_ctor_set_uint64(v_reuseFailAlloc_2678_, sizeof(void*)*1, v_tid_2665_);
v___x_2672_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 4, v___x_2672_);
v___x_2674_ = v___x_2663_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_env_2654_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_nextMacroScope_2655_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_ngen_2656_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v_auxDeclNGen_2657_);
lean_ctor_set(v_reuseFailAlloc_2677_, 4, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2677_, 5, v_cache_2658_);
lean_ctor_set(v_reuseFailAlloc_2677_, 6, v_messages_2659_);
lean_ctor_set(v_reuseFailAlloc_2677_, 7, v_infoState_2660_);
lean_ctor_set(v_reuseFailAlloc_2677_, 8, v_snapshotTasks_2661_);
v___x_2674_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_st_ref_put(v___y_2612_, v___x_2674_);
v___x_2676_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_fst_2614_);
return v___x_2676_;
}
}
}
}
}
else
{
goto v___jp_2645_;
}
}
else
{
goto v___jp_2645_;
}
}
v___jp_2681_:
{
double v___x_2683_; double v___x_2684_; double v___x_2685_; uint8_t v___x_2686_; 
v___x_2683_ = lean_unbox_float(v_snd_2631_);
v___x_2684_ = lean_unbox_float(v_fst_2630_);
v___x_2685_ = lean_float_sub(v___x_2683_, v___x_2684_);
v___x_2686_ = lean_float_decLt(v___y_2682_, v___x_2685_);
v___y_2651_ = v___x_2686_;
goto v___jp_2650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(lean_object* v_cls_2697_, lean_object* v_collapsed_2698_, lean_object* v_tag_2699_, lean_object* v_opts_2700_, lean_object* v_clsEnabled_2701_, lean_object* v_oldTraces_2702_, lean_object* v_msg_2703_, lean_object* v_resStartStop_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
uint8_t v_collapsed_boxed_2710_; uint8_t v_clsEnabled_boxed_2711_; lean_object* v_res_2712_; 
v_collapsed_boxed_2710_ = lean_unbox(v_collapsed_2698_);
v_clsEnabled_boxed_2711_ = lean_unbox(v_clsEnabled_2701_);
v_res_2712_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2697_, v_collapsed_boxed_2710_, v_tag_2699_, v_opts_2700_, v_clsEnabled_boxed_2711_, v_oldTraces_2702_, v_msg_2703_, v_resStartStop_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec_ref(v_opts_2700_);
return v_res_2712_;
}
}
static double _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0(void){
_start:
{
lean_object* v___x_2713_; double v___x_2714_; 
v___x_2713_ = lean_unsigned_to_nat(1000000000u);
v___x_2714_ = lean_float_of_nat(v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(lean_object* v_t_2715_, lean_object* v_s_2716_, lean_object* v_candidate_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_options_2723_; lean_object* v_toCold_2724_; uint8_t v_hasTrace_2725_; uint8_t v___x_2726_; 
v_options_2723_ = lean_ctor_get(v_a_2720_, 1);
v_toCold_2724_ = lean_ctor_get(v_a_2720_, 0);
v_hasTrace_2725_ = lean_ctor_get_uint8(v_options_2723_, sizeof(void*)*1);
v___x_2726_ = 1;
if (v_hasTrace_2725_ == 0)
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2717_, v_t_2715_, v_s_2716_, v___x_2726_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
return v___x_2727_;
}
else
{
lean_object* v_inheritedTraceOptions_2728_; lean_object* v___f_2729_; lean_object* v_cls_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v_a_2737_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v_a_2752_; 
v_inheritedTraceOptions_2728_ = lean_ctor_get(v_toCold_2724_, 4);
lean_inc_ref(v_s_2716_);
lean_inc_ref(v_t_2715_);
lean_inc(v_candidate_2717_);
v___f_2729_ = lean_alloc_closure((void*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2729_, 0, v_candidate_2717_);
lean_closure_set(v___f_2729_, 1, v_t_2715_);
lean_closure_set(v___f_2729_, 2, v_s_2716_);
v_cls_2730_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2731_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1));
v___x_2732_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2733_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2728_, v_options_2723_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2802_ = l_Lean_trace_profiler;
v___x_2803_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2723_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
lean_dec_ref(v___f_2729_);
v___x_2804_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2717_, v_t_2715_, v_s_2716_, v___x_2726_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
return v___x_2804_;
}
else
{
goto v___jp_2761_;
}
}
else
{
goto v___jp_2761_;
}
v___jp_2734_:
{
lean_object* v___x_2738_; double v___x_2739_; double v___x_2740_; double v___x_2741_; double v___x_2742_; double v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2738_ = lean_io_mono_nanos_now();
v___x_2739_ = lean_float_of_nat(v___y_2736_);
v___x_2740_ = lean_float_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0);
v___x_2741_ = lean_float_div(v___x_2739_, v___x_2740_);
v___x_2742_ = lean_float_of_nat(v___x_2738_);
v___x_2743_ = lean_float_div(v___x_2742_, v___x_2740_);
v___x_2744_ = lean_box_float(v___x_2741_);
v___x_2745_ = lean_box_float(v___x_2743_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v_a_2737_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2730_, v___x_2726_, v___x_2731_, v_options_2723_, v___x_2733_, v___y_2735_, v___f_2729_, v___x_2747_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
return v___x_2748_;
}
v___jp_2749_:
{
lean_object* v___x_2753_; double v___x_2754_; double v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2753_ = lean_io_get_num_heartbeats();
v___x_2754_ = lean_float_of_nat(v___y_2751_);
v___x_2755_ = lean_float_of_nat(v___x_2753_);
v___x_2756_ = lean_box_float(v___x_2754_);
v___x_2757_ = lean_box_float(v___x_2755_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_a_2752_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_2730_, v___x_2726_, v___x_2731_, v_options_2723_, v___x_2733_, v___y_2750_, v___f_2729_, v___x_2759_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
return v___x_2760_;
}
v___jp_2761_:
{
lean_object* v___x_2762_; lean_object* v_a_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2762_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v_a_2721_);
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref(v___x_2762_);
v___x_2764_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2765_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_2723_, v___x_2764_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_io_mono_nanos_now();
v___x_2767_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2717_, v_t_2715_, v_s_2716_, v___x_2726_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2767_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2767_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 1);
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
v___y_2735_ = v_a_2763_;
v___y_2736_ = v___x_2766_;
v_a_2737_ = v___x_2773_;
goto v___jp_2734_;
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
v_a_2776_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2767_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2767_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
lean_ctor_set_tag(v___x_2778_, 0);
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
v___y_2735_ = v_a_2763_;
v___y_2736_ = v___x_2766_;
v_a_2737_ = v___x_2781_;
goto v___jp_2734_;
}
}
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_io_get_num_heartbeats();
v___x_2785_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_2717_, v_t_2715_, v_s_2716_, v___x_2726_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set_tag(v___x_2788_, 1);
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
v___y_2750_ = v_a_2763_;
v___y_2751_ = v___x_2784_;
v_a_2752_ = v___x_2791_;
goto v___jp_2749_;
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_a_2794_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2785_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2785_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set_tag(v___x_2796_, 0);
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
v___y_2750_ = v_a_2763_;
v___y_2751_ = v___x_2784_;
v_a_2752_ = v___x_2799_;
goto v___jp_2749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(lean_object* v_t_2805_, lean_object* v_s_2806_, lean_object* v_candidate_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2805_, v_s_2806_, v_candidate_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object* v_as_2814_, lean_object* v_as_x27_2815_, lean_object* v_b_2816_, lean_object* v_a_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_2815_, v_b_2816_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object* v_as_2824_, lean_object* v_as_x27_2825_, lean_object* v_b_2826_, lean_object* v_a_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(v_as_2824_, v_as_x27_2825_, v_b_2826_, v_a_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_as_x27_2825_);
lean_dec(v_as_2824_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(lean_object* v_00_u03b1_2834_, lean_object* v_x_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___redArg(v_x_2835_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2842_, lean_object* v_x_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_00_u03b1_2842_, v_x_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(lean_object* v_t_2850_, lean_object* v_s_2851_, uint8_t v___x_2852_, lean_object* v_as_2853_, size_t v_sz_2854_, size_t v_i_2855_, lean_object* v_b_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v___x_2862_; 
v___x_2862_ = lean_usize_dec_lt(v_i_2855_, v_sz_2854_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; 
lean_dec_ref(v_s_2851_);
lean_dec_ref(v_t_2850_);
v___x_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2863_, 0, v_b_2856_);
return v___x_2863_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2865_; 
lean_dec_ref(v_b_2856_);
v_a_2864_ = lean_array_uget_borrowed(v_as_2853_, v_i_2855_);
lean_inc(v_a_2864_);
lean_inc_ref(v_s_2851_);
lean_inc_ref(v_t_2850_);
v___x_2865_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_2850_, v_s_2851_, v_a_2864_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2882_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2882_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2882_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = lean_box(0);
v___x_2871_ = lean_unbox(v_a_2866_);
lean_dec(v_a_2866_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; size_t v___x_2873_; size_t v___x_2874_; 
lean_del_object(v___x_2868_);
v___x_2872_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v___x_2873_ = ((size_t)1ULL);
v___x_2874_ = lean_usize_add(v_i_2855_, v___x_2873_);
v_i_2855_ = v___x_2874_;
v_b_2856_ = v___x_2872_;
goto _start;
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
lean_dec_ref(v_s_2851_);
lean_dec_ref(v_t_2850_);
v___x_2876_ = lean_box(v___x_2852_);
v___x_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
lean_ctor_set(v___x_2878_, 1, v___x_2870_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2878_);
v___x_2880_ = v___x_2868_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
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
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec_ref(v_s_2851_);
lean_dec_ref(v_t_2850_);
v_a_2883_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2865_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2865_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object* v_t_2891_, lean_object* v_s_2892_, lean_object* v___x_2893_, lean_object* v_as_2894_, lean_object* v_sz_2895_, lean_object* v_i_2896_, lean_object* v_b_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
uint8_t v___x_2948__boxed_2903_; size_t v_sz_boxed_2904_; size_t v_i_boxed_2905_; lean_object* v_res_2906_; 
v___x_2948__boxed_2903_ = lean_unbox(v___x_2893_);
v_sz_boxed_2904_ = lean_unbox_usize(v_sz_2895_);
lean_dec(v_sz_2895_);
v_i_boxed_2905_ = lean_unbox_usize(v_i_2896_);
lean_dec(v_i_2896_);
v_res_2906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2891_, v_s_2892_, v___x_2948__boxed_2903_, v_as_2894_, v_sz_boxed_2904_, v_i_boxed_2905_, v_b_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v_as_2894_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* v_t_2907_, lean_object* v_s_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_options_2914_; lean_object* v_toCold_2915_; uint8_t v_hasTrace_2916_; lean_object* v___x_2917_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; 
v_options_2914_ = lean_ctor_get(v_a_2911_, 1);
v_toCold_2915_ = lean_ctor_get(v_a_2911_, 0);
v_hasTrace_2916_ = lean_ctor_get_uint8(v_options_2914_, sizeof(void*)*1);
v___x_2917_ = lean_obj_once(&l_Lean_Meta_instInhabitedUnificationHints_default___closed__0, &l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once, _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0);
if (v_hasTrace_2916_ == 0)
{
v___y_2919_ = v_a_2909_;
v___y_2920_ = v_a_2910_;
v___y_2921_ = v_a_2911_;
v___y_2922_ = v_a_2912_;
goto v___jp_2918_;
}
else
{
lean_object* v_inheritedTraceOptions_2989_; lean_object* v_cls_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; 
v_inheritedTraceOptions_2989_ = lean_ctor_get(v_toCold_2915_, 4);
v_cls_2990_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_2991_ = lean_obj_once(&l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8, &l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once, _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
v___x_2992_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2989_, v_options_2914_, v___x_2991_);
if (v___x_2992_ == 0)
{
v___y_2919_ = v_a_2909_;
v___y_2920_ = v_a_2910_;
v___y_2921_ = v_a_2911_;
v___y_2922_ = v_a_2912_;
goto v___jp_2918_;
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_inc_ref(v_t_2907_);
v___x_2993_ = l_Lean_MessageData_ofExpr(v_t_2907_);
v___x_2994_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
lean_inc_ref(v_s_2908_);
v___x_2996_ = l_Lean_MessageData_ofExpr(v_s_2908_);
v___x_2997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2995_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_2990_, v___x_2997_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_dec_ref_known(v___x_2998_, 1);
v___y_2919_ = v_a_2909_;
v___y_2920_ = v_a_2910_;
v___y_2921_ = v_a_2911_;
v___y_2922_ = v_a_2912_;
goto v___jp_2918_;
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_s_2908_);
lean_dec_ref(v_t_2907_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
v___jp_2918_:
{
lean_object* v___x_2923_; uint8_t v_unificationHints_2924_; 
v___x_2923_ = l_Lean_Meta_Context_config(v___y_2919_);
v_unificationHints_2924_ = lean_ctor_get_uint8(v___x_2923_, 5);
lean_dec_ref(v___x_2923_);
if (v_unificationHints_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec_ref(v_s_2908_);
lean_dec_ref(v_t_2907_);
v___x_2925_ = lean_box(v_unificationHints_2924_);
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
return v___x_2926_;
}
else
{
uint8_t v___x_2927_; 
v___x_2927_ = l_Lean_Expr_isMVar(v_t_2907_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v_env_2929_; lean_object* v___x_2930_; lean_object* v_ext_2931_; lean_object* v_toEnvExtension_2932_; lean_object* v_asyncMode_2933_; lean_object* v___x_2934_; lean_object* v_config_2935_; uint8_t v_trackZetaDelta_2936_; lean_object* v_zetaDeltaSet_2937_; lean_object* v_lctx_2938_; lean_object* v_localInstances_2939_; lean_object* v_defEqCtx_x3f_2940_; lean_object* v_synthPendingDepth_2941_; lean_object* v_customCanUnfoldPredicate_x3f_2942_; uint8_t v_univApprox_2943_; uint8_t v_inTypeClassResolution_2944_; uint8_t v_cacheInferType_2945_; uint64_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2928_ = lean_st_ref_get(v___y_2922_);
v_env_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc_ref(v_env_2929_);
lean_dec(v___x_2928_);
v___x_2930_ = l_Lean_Meta_unificationHintExtension;
v_ext_2931_ = lean_ctor_get(v___x_2930_, 1);
v_toEnvExtension_2932_ = lean_ctor_get(v_ext_2931_, 0);
v_asyncMode_2933_ = lean_ctor_get(v_toEnvExtension_2932_, 2);
v___x_2934_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
v_config_2935_ = lean_ctor_get(v___x_2934_, 0);
v_trackZetaDelta_2936_ = lean_ctor_get_uint8(v___y_2919_, sizeof(void*)*7);
v_zetaDeltaSet_2937_ = lean_ctor_get(v___y_2919_, 1);
v_lctx_2938_ = lean_ctor_get(v___y_2919_, 2);
v_localInstances_2939_ = lean_ctor_get(v___y_2919_, 3);
v_defEqCtx_x3f_2940_ = lean_ctor_get(v___y_2919_, 4);
v_synthPendingDepth_2941_ = lean_ctor_get(v___y_2919_, 5);
v_customCanUnfoldPredicate_x3f_2942_ = lean_ctor_get(v___y_2919_, 6);
v_univApprox_2943_ = lean_ctor_get_uint8(v___y_2919_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2944_ = lean_ctor_get_uint8(v___y_2919_, sizeof(void*)*7 + 2);
v_cacheInferType_2945_ = lean_ctor_get_uint8(v___y_2919_, sizeof(void*)*7 + 3);
v___x_2946_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2935_);
v___x_2947_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2917_, v___x_2930_, v_env_2929_, v_asyncMode_2933_);
lean_inc_ref(v_config_2935_);
v___x_2948_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2948_, 0, v_config_2935_);
lean_ctor_set_uint64(v___x_2948_, sizeof(void*)*1, v___x_2946_);
lean_inc(v_customCanUnfoldPredicate_x3f_2942_);
lean_inc(v_synthPendingDepth_2941_);
lean_inc(v_defEqCtx_x3f_2940_);
lean_inc_ref(v_localInstances_2939_);
lean_inc_ref(v_lctx_2938_);
lean_inc(v_zetaDeltaSet_2937_);
v___x_2949_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v_zetaDeltaSet_2937_);
lean_ctor_set(v___x_2949_, 2, v_lctx_2938_);
lean_ctor_set(v___x_2949_, 3, v_localInstances_2939_);
lean_ctor_set(v___x_2949_, 4, v_defEqCtx_x3f_2940_);
lean_ctor_set(v___x_2949_, 5, v_synthPendingDepth_2941_);
lean_ctor_set(v___x_2949_, 6, v_customCanUnfoldPredicate_x3f_2942_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*7, v_trackZetaDelta_2936_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*7 + 1, v_univApprox_2943_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2944_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*7 + 3, v_cacheInferType_2945_);
lean_inc_ref(v_t_2907_);
v___x_2950_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v___x_2947_, v_t_2907_, v___x_2949_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec_ref_known(v___x_2949_, 7);
lean_dec(v___x_2947_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; size_t v_sz_2953_; size_t v___x_2954_; lean_object* v___x_2955_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v___x_2952_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0));
v_sz_2953_ = lean_array_size(v_a_2951_);
v___x_2954_ = ((size_t)0ULL);
v___x_2955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_2907_, v_s_2908_, v_unificationHints_2924_, v_a_2951_, v_sz_2953_, v___x_2954_, v___x_2952_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v_a_2951_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2969_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2969_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2969_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v_fst_2960_; 
v_fst_2960_ = lean_ctor_get(v_a_2956_, 0);
lean_inc(v_fst_2960_);
lean_dec(v_a_2956_);
if (lean_obj_tag(v_fst_2960_) == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2961_ = lean_box(v___x_2927_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2961_);
v___x_2963_ = v___x_2958_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
else
{
lean_object* v_val_2965_; lean_object* v___x_2967_; 
v_val_2965_ = lean_ctor_get(v_fst_2960_, 0);
lean_inc(v_val_2965_);
lean_dec_ref_known(v_fst_2960_, 1);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v_val_2965_);
v___x_2967_ = v___x_2958_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_val_2965_);
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
v_a_2970_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2955_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2955_);
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
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec_ref(v_s_2908_);
lean_dec_ref(v_t_2907_);
v_a_2978_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2950_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2950_);
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
else
{
uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_dec_ref(v_s_2908_);
lean_dec_ref(v_t_2907_);
v___x_2986_ = 0;
v___x_2987_ = lean_box(v___x_2986_);
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
return v___x_2988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___boxed(lean_object* v_t_3007_, lean_object* v_s_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Meta_tryUnificationHints(v_t_3007_, v_s_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
return v_res_3014_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_unsigned_to_nat(2674080740u);
v___x_3016_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3017_ = l_Lean_Name_num___override(v___x_3016_, v___x_3015_);
return v___x_3017_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3019_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3020_ = l_Lean_Name_str___override(v___x_3019_, v___x_3018_);
return v___x_3020_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = ((lean_object*)(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_));
v___x_3022_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3023_ = l_Lean_Name_str___override(v___x_3022_, v___x_3021_);
return v___x_3023_;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_unsigned_to_nat(2u);
v___x_3025_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3026_ = l_Lean_Name_num___override(v___x_3025_, v___x_3024_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3028_ = ((lean_object*)(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5));
v___x_3029_ = 0;
v___x_3030_ = lean_obj_once(&l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_, &l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
v___x_3031_ = l_Lean_registerTraceClass(v___x_3028_, v___x_3029_, v___x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
return v_res_3033_;
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
