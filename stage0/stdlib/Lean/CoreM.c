// Lean compiler output
// Module: Lean.CoreM
// Imports: Init Lean.Util.RecDepth Lean.Util.Trace Lean.Log Lean.Data.Options Lean.Environment Lean.Exception Lean.InternalExceptionId Lean.Eval Lean.MonadEnv Lean.ResolveName
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
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadTraceCoreM___closed__3;
static lean_object* l_Lean_Core_State_ngen___default___closed__3;
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2;
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_maxHeartbeats___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Core_instMonadEnvCoreM___closed__2;
lean_object* lean_io_get_num_heartbeats(lean_object*);
static lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___closed__3;
static lean_object* l_Lean_Core_instInhabitedState___closed__12;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCache;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_Cache_instLevelType___default___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__2;
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__4;
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_Lean_Core_restore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Cache_instLevelType___default;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Core_instInhabitedState___closed__11;
LEAN_EXPORT lean_object* l_Lean_Core_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_State_nextMacroScope___default___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_options___default;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM;
static lean_object* l_Lean_Core_Cache_instLevelType___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadEnvCoreM___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1;
static lean_object* l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_currMacroScope___default;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_maxHeartbeats;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_catchInternalIds___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Core_instantiateTypeLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Cache_instLevelValue___default;
extern lean_object* l_Lean_maxRecDepth;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__2;
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forM___at_Lean_Core_instMetaEvalCoreM___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM;
static lean_object* l_Lean_Core_instMonadRefCoreM___closed__2;
static lean_object* l_Lean_Core_instMonadTraceCoreM___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_State_traceState___default___closed__1;
static lean_object* l_Lean_Core_instMonadCoreM___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_State_traceState___default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___rarg(lean_object*);
static lean_object* l_Lean_Core_State_traceState___default___closed__3;
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_currNamespace___default;
static lean_object* l_Lean_Core_instMonadRefCoreM___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedState___closed__10;
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_openDecls___default;
static lean_object* l_Lean_Core_instMonadResolveNameCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___rarg___boxed(lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2;
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_27____spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_ref___default;
static lean_object* l_Lean_Core_instInhabitedState___closed__7;
static lean_object* l_Lean_Core_instInhabitedCoreM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__5;
static lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__2;
static lean_object* l_Lean_Core_instMonadResolveNameCoreM___closed__1;
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_State_messages___default;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadTraceCoreM___closed__1;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__1;
static lean_object* l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__4;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__6;
extern lean_object* l_Lean_firstFrontendMacroScope;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forMAux___at_Lean_Core_instMetaEvalCoreM___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_maxRecDepth___default;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_State_nextMacroScope___default;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMetaEvalCoreM___rarg(lean_object*);
lean_object* l_EStateM_instMonadEStateM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_initHeartbeats___default;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMetaEvalCoreM(lean_object*);
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__4;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__4;
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
static lean_object* l_Lean_Core_instInhabitedState___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_Cache_instLevelType___default___closed__3;
static lean_object* l_Lean_Core_getMaxHeartbeats___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCache___closed__1;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedState___closed__5;
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__1;
static lean_object* l_Lean_Core_instAddMessageContextCoreM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_State_traceState___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object*);
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3;
static lean_object* l_Lean_Core_instMonadCoreM___closed__4;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_State_ngen___default;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l_Lean_Core_State_ngen___default___closed__2;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__5;
static lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__3;
static lean_object* l_Lean_Core_instMonadResolveNameCoreM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_State_traceState___default;
static lean_object* l_Lean_Core_instMonadCoreM___closed__2;
static lean_object* l_Lean_Core_instMonadEnvCoreM___closed__3;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static size_t l_Lean_Core_instInhabitedState___closed__9;
lean_object* l_IO_println___at_Lean_instEval__1___spec__1(lean_object*, lean_object*);
static uint32_t l_Lean_Core_instInhabitedState___closed__4;
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_State_cache___default;
LEAN_EXPORT lean_object* l_Lean_catchInternalId___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__5;
static lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___closed__1;
static lean_object* l_Lean_Core_CoreM_toIO___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2;
static lean_object* l_Lean_Core_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_currRecDepth___default;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object*);
static lean_object* l_Lean_Core_instInhabitedState___closed__2;
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_State_ngen___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instAddMessageContextCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object*);
static lean_object* l_Lean_Core_instInhabitedCoreM___rarg___closed__2;
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8___boxed(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM;
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_Core_instMonadRefCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedState;
static lean_object* l_Lean_Core_instInhabitedState___closed__8;
static lean_object* l_Lean_Exception_isMaxHeartbeat___closed__1;
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7_(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_catchInternalIds___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_Context_maxHeartbeats___default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maxHeartbeats", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maximum amount of heartbeats per command. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit", 126);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(200000u);
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__3;
x_3 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__2;
x_3 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__5;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_27____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_getMaxHeartbeats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_maxHeartbeats;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Core_getMaxHeartbeats___closed__1;
x_3 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_1, x_2);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_Cache_instLevelType___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Cache_instLevelType___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_Cache_instLevelType___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_Cache_instLevelType___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Cache_instLevelType___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Cache_instLevelType___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_Cache_instLevelType___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Cache_instLevelValue___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_Cache_instLevelType___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_Cache_instLevelType___default___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instInhabitedCache___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_State_nextMacroScope___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_State_nextMacroScope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_State_nextMacroScope___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_State_ngen___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_uniq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_State_ngen___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_State_ngen___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_State_ngen___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_State_ngen___default___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_State_ngen___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_State_ngen___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_State_traceState___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_State_traceState___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_State_traceState___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_State_traceState___default___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Core_State_traceState___default___closed__2;
x_3 = l_Lean_Core_State_traceState___default___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_State_traceState___default___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_Core_State_traceState___default___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_State_traceState___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_State_traceState___default___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_State_cache___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instInhabitedCache___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_State_messages___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_State_traceState___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Core_instInhabitedState___closed__1;
x_3 = l_Lean_Core_Cache_instLevelType___default___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint32_t _init_l_Lean_Core_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__5() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_instInhabitedState___closed__4;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Lean_Core_instInhabitedState___closed__3;
x_5 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*5 + 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_instInhabitedState___closed__1;
x_2 = l_Lean_Core_instInhabitedState___closed__2;
x_3 = l_Lean_Core_instInhabitedState___closed__3;
x_4 = l_Lean_Core_instInhabitedState___closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instInhabitedState___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Core_instInhabitedState___closed__9() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Core_instInhabitedState___closed__8;
x_2 = l_Lean_Core_instInhabitedState___closed__3;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Core_instInhabitedState___closed__9;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__11() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Core_instInhabitedState___closed__10;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Core_instInhabitedState___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Core_instInhabitedState___closed__7;
x_4 = l_Lean_Core_instInhabitedState___closed__11;
x_5 = l_Lean_Core_instInhabitedCache___closed__1;
x_6 = l_Lean_Core_instInhabitedState___closed__10;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instInhabitedState___closed__12;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Context_options___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Context_currRecDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Context_maxRecDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1000u);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Context_ref___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Context_currNamespace___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Context_openDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Context_initHeartbeats___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_Context_maxHeartbeats___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_Context_maxHeartbeats___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_Context_maxHeartbeats___default(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_Context_currMacroScope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_firstFrontendMacroScope;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_apply_3(x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_4(x_4, x_9, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_instMonadEStateM(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_Core_instMonadCoreM___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
x_5 = l_Lean_Core_instMonadCoreM___closed__4;
lean_ctor_set(x_2, 1, x_5);
x_6 = l_Lean_Core_instMonadCoreM___closed__5;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_12 = l_Lean_Core_instMonadCoreM___closed__4;
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
x_14 = l_Lean_Core_instMonadCoreM___closed__5;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadCoreM___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instMonadCoreM___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCoreM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCoreM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_instInhabitedCoreM___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Core_instInhabitedCoreM___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___rarg), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instInhabitedCoreM(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 5);
lean_dec(x_8);
lean_ctor_set(x_4, 5, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 6);
x_16 = lean_ctor_get(x_4, 7);
x_17 = lean_ctor_get(x_4, 8);
x_18 = lean_ctor_get(x_4, 9);
x_19 = lean_ctor_get(x_4, 10);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_20 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set(x_20, 2, x_12);
lean_ctor_set(x_20, 3, x_13);
lean_ctor_set(x_20, 4, x_14);
lean_ctor_set(x_20, 5, x_2);
lean_ctor_set(x_20, 6, x_15);
lean_ctor_set(x_20, 7, x_16);
lean_ctor_set(x_20, 8, x_17);
lean_ctor_set(x_20, 9, x_18);
lean_ctor_set(x_20, 10, x_19);
x_21 = lean_apply_3(x_3, x_20, x_5, x_6);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadRefCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRefCoreM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadRefCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRefCoreM___lambda__2), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadRefCoreM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadRefCoreM___closed__1;
x_2 = l_Lean_Core_instMonadRefCoreM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instMonadRefCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadRefCoreM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRefCoreM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 4);
lean_dec(x_10);
x_11 = lean_apply_1(x_1, x_9);
x_12 = l_Lean_Core_instInhabitedCache___closed__1;
lean_ctor_set(x_6, 4, x_12);
lean_ctor_set(x_6, 0, x_11);
x_13 = lean_st_ref_set(x_3, x_6, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_25 = lean_apply_1(x_1, x_20);
x_26 = l_Lean_Core_instInhabitedCache___closed__1;
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_24);
x_28 = lean_st_ref_set(x_3, x_27, x_7);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadEnvCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadEnvCoreM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadEnvCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadEnvCoreM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadEnvCoreM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadEnvCoreM___closed__1;
x_2 = l_Lean_Core_instMonadEnvCoreM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instMonadEnvCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadEnvCoreM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadEnvCoreM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadEnvCoreM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadOptionsCoreM(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_3, 2, x_8);
x_9 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_ctor_get(x_3, 6);
x_17 = lean_ctor_get(x_3, 7);
x_18 = lean_ctor_get(x_3, 8);
x_19 = lean_ctor_get(x_3, 9);
x_20 = lean_ctor_get(x_3, 10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_21 = lean_apply_1(x_1, x_12);
x_22 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_13);
lean_ctor_set(x_22, 4, x_14);
lean_ctor_set(x_22, 5, x_15);
lean_ctor_set(x_22, 6, x_16);
lean_ctor_set(x_22, 7, x_17);
lean_ctor_set(x_22, 8, x_18);
lean_ctor_set(x_22, 9, x_19);
lean_ctor_set(x_22, 10, x_20);
x_23 = lean_apply_3(x_2, x_22, x_4, x_5);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadWithOptionsCoreM___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Cache_instLevelType___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Cache_instLevelType___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1;
x_3 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2;
x_4 = l_Lean_Core_Cache_instLevelType___default___closed__3;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_4);
lean_ctor_set(x_6, 5, x_2);
lean_ctor_set(x_6, 6, x_3);
lean_ctor_set(x_6, 7, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*8, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Cache_instLevelType___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
x_2 = l_Lean_Core_State_traceState___default___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 2);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3;
x_11 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5;
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
x_13 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3;
x_19 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5;
lean_inc(x_17);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_17);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Core_instAddMessageContextCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instAddMessageContextCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 2);
lean_dec(x_9);
lean_ctor_set(x_6, 2, x_1);
x_10 = lean_st_ref_set(x_3, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_1);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_st_ref_set(x_3, x_22, x_7);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadNameGeneratorCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadNameGeneratorCoreM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadNameGeneratorCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadNameGeneratorCoreM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadNameGeneratorCoreM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadNameGeneratorCoreM___closed__1;
x_2 = l_Lean_Core_instMonadNameGeneratorCoreM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instMonadNameGeneratorCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadNameGeneratorCoreM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadNameGeneratorCoreM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadNameGeneratorCoreM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 3);
lean_dec(x_8);
lean_ctor_set(x_4, 3, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 5);
x_15 = lean_ctor_get(x_4, 6);
x_16 = lean_ctor_get(x_4, 7);
x_17 = lean_ctor_get(x_4, 8);
x_18 = lean_ctor_get(x_4, 9);
x_19 = lean_ctor_get(x_4, 10);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_20 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set(x_20, 2, x_12);
lean_ctor_set(x_20, 3, x_2);
lean_ctor_set(x_20, 4, x_13);
lean_ctor_set(x_20, 5, x_14);
lean_ctor_set(x_20, 6, x_15);
lean_ctor_set(x_20, 7, x_16);
lean_ctor_set(x_20, 8, x_17);
lean_ctor_set(x_20, 9, x_18);
lean_ctor_set(x_20, 10, x_19);
x_21 = lean_apply_3(x_3, x_20, x_5, x_6);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instMonadRecDepthCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRecDepthCoreM___lambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadRecDepthCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRecDepthCoreM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadRecDepthCoreM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRecDepthCoreM___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadRecDepthCoreM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_instMonadRecDepthCoreM___closed__1;
x_2 = l_Lean_Core_instMonadRecDepthCoreM___closed__2;
x_3 = l_Lean_Core_instMonadRecDepthCoreM___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_instMonadRecDepthCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadRecDepthCoreM___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRecDepthCoreM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRecDepthCoreM___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 6);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 7);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instMonadResolveNameCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadResolveNameCoreM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadResolveNameCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadResolveNameCoreM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadResolveNameCoreM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadResolveNameCoreM___closed__1;
x_2 = l_Lean_Core_instMonadResolveNameCoreM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instMonadResolveNameCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadResolveNameCoreM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadResolveNameCoreM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadResolveNameCoreM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_ctor_set(x_6, 1, x_11);
x_12 = lean_st_ref_set(x_3, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 10);
lean_dec(x_15);
lean_ctor_set(x_2, 10, x_9);
x_16 = lean_apply_3(x_1, x_2, x_3, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 5);
x_23 = lean_ctor_get(x_2, 6);
x_24 = lean_ctor_get(x_2, 7);
x_25 = lean_ctor_get(x_2, 8);
x_26 = lean_ctor_get(x_2, 9);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_20);
lean_ctor_set(x_27, 4, x_21);
lean_ctor_set(x_27, 5, x_22);
lean_ctor_set(x_27, 6, x_23);
lean_ctor_set(x_27, 7, x_24);
lean_ctor_set(x_27, 8, x_25);
lean_ctor_set(x_27, 9, x_26);
lean_ctor_set(x_27, 10, x_9);
x_28 = lean_apply_3(x_1, x_27, x_3, x_13);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_ctor_get(x_6, 3);
x_33 = lean_ctor_get(x_6, 4);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_30, x_35);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_34);
x_38 = lean_st_ref_set(x_3, x_37, x_7);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 6);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 7);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 8);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 9);
lean_inc(x_49);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 lean_ctor_release(x_2, 10);
 x_50 = x_2;
} else {
 lean_dec_ref(x_2);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 11, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_41);
lean_ctor_set(x_51, 2, x_42);
lean_ctor_set(x_51, 3, x_43);
lean_ctor_set(x_51, 4, x_44);
lean_ctor_set(x_51, 5, x_45);
lean_ctor_set(x_51, 6, x_46);
lean_ctor_set(x_51, 7, x_47);
lean_ctor_set(x_51, 8, x_48);
lean_ctor_set(x_51, 9, x_49);
lean_ctor_set(x_51, 10, x_30);
x_52 = lean_apply_3(x_1, x_51, x_3, x_39);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_withFreshMacroScope___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 10);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_environment_main_module(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_environment_main_module(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withFreshMacroScope___rarg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_instMonadQuotationCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadQuotationCoreM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadQuotationCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadQuotationCoreM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadQuotationCoreM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadQuotationCoreM___lambda__3), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadQuotationCoreM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_instMonadRefCoreM;
x_2 = l_Lean_Core_instMonadQuotationCoreM___closed__1;
x_3 = l_Lean_Core_instMonadQuotationCoreM___closed__2;
x_4 = l_Lean_Core_instMonadQuotationCoreM___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instMonadQuotationCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadQuotationCoreM___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadQuotationCoreM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadQuotationCoreM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 4);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 4, x_10);
x_11 = lean_st_ref_set(x_3, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_24 = lean_apply_1(x_1, x_22);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_23);
x_26 = lean_st_ref_set(x_3, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyCache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 4);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_7, 0, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_apply_1(x_1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_6, 4, x_24);
x_25 = lean_st_ref_set(x_3, x_6, x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_37 = x_7;
} else {
 lean_dec_ref(x_7);
 x_37 = lean_box(0);
}
x_38 = lean_apply_1(x_1, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set(x_40, 3, x_33);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_34);
x_41 = lean_st_ref_set(x_3, x_40, x_8);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyInstLevelTypeCache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 4);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_7, 1, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_apply_1(x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_6, 4, x_24);
x_25 = lean_st_ref_set(x_3, x_6, x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_37 = x_7;
} else {
 lean_dec_ref(x_7);
 x_37 = lean_box(0);
}
x_38 = lean_apply_1(x_1, x_36);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set(x_40, 3, x_33);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_34);
x_41 = lean_st_ref_set(x_3, x_40, x_8);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyInstLevelValueCache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash___override(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Core_instantiateTypeLevelParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Core_instantiateTypeLevelParams___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Core_instantiateTypeLevelParams___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Name_hash___override(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_level_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_instantiate_type_lparams(x_1, x_2);
x_8 = lean_st_ref_take(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 4);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_7);
x_18 = l_Std_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_15, x_16, x_17);
lean_ctor_set(x_10, 0, x_18);
x_19 = lean_st_ref_set(x_5, x_9, x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_7);
x_28 = l_Std_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_24, x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_9, 4, x_29);
x_30 = lean_st_ref_set(x_5, x_9, x_11);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get(x_9, 2);
x_37 = lean_ctor_get(x_9, 3);
x_38 = lean_ctor_get(x_9, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_41 = x_10;
} else {
 lean_dec_ref(x_10);
 x_41 = lean_box(0);
}
x_42 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_7);
x_44 = l_Std_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_39, x_42, x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_38);
x_47 = lean_st_ref_set(x_5, x_46, x_11);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 4);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_ConstantInfo_name(x_1);
x_13 = l_Std_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_14 = lean_box(0);
x_15 = l_Lean_Core_instantiateTypeLevelParams___lambda__1(x_1, x_2, x_14, x_3, x_4, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(x_2, x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_free_object(x_6);
x_20 = lean_box(0);
x_21 = l_Lean_Core_instantiateTypeLevelParams___lambda__1(x_1, x_2, x_20, x_3, x_4, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_6, 0, x_18);
return x_6;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_ctor_get(x_22, 4);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_ConstantInfo_name(x_1);
x_27 = l_Std_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(x_25, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Core_instantiateTypeLevelParams___lambda__1(x_1, x_2, x_28, x_3, x_4, x_23);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(x_2, x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = l_Lean_Core_instantiateTypeLevelParams___lambda__1(x_1, x_2, x_34, x_3, x_4, x_23);
lean_dec(x_4);
lean_dec(x_3);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_23);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_instantiateTypeLevelParams___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateTypeLevelParams(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_instantiate_value_lparams(x_1, x_2);
x_8 = lean_st_ref_take(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 4);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_10, 1);
x_16 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_7);
x_18 = l_Std_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_15, x_16, x_17);
lean_ctor_set(x_10, 1, x_18);
x_19 = lean_st_ref_set(x_5, x_9, x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_7);
x_28 = l_Std_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_25, x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_9, 4, x_29);
x_30 = lean_st_ref_set(x_5, x_9, x_11);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get(x_9, 2);
x_37 = lean_ctor_get(x_9, 3);
x_38 = lean_ctor_get(x_9, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_41 = x_10;
} else {
 lean_dec_ref(x_10);
 x_41 = lean_box(0);
}
x_42 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_7);
x_44 = l_Std_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_40, x_42, x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_38);
x_47 = lean_st_ref_set(x_5, x_46, x_11);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 4);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_ConstantInfo_name(x_1);
x_13 = l_Std_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_14 = lean_box(0);
x_15 = l_Lean_Core_instantiateValueLevelParams___lambda__1(x_1, x_2, x_14, x_3, x_4, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(x_2, x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_free_object(x_6);
x_20 = lean_box(0);
x_21 = l_Lean_Core_instantiateValueLevelParams___lambda__1(x_1, x_2, x_20, x_3, x_4, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_6, 0, x_18);
return x_6;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_ctor_get(x_22, 4);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_ConstantInfo_name(x_1);
x_27 = l_Std_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(x_25, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Core_instantiateValueLevelParams___lambda__1(x_1, x_2, x_28, x_3, x_4, x_23);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(x_2, x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = l_Lean_Core_instantiateValueLevelParams___lambda__1(x_1, x_2, x_34, x_3, x_4, x_23);
lean_dec(x_4);
lean_dec(x_3);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_23);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_instantiateValueLevelParams___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateValueLevelParams(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_io_error_to_string(x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_io_error_to_string(x_17);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_liftIOCore___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_io_error_to_string(x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_io_error_to_string(x_17);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLiftIOCoreM___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadLiftIOCoreM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 3, x_10);
x_11 = lean_st_ref_set(x_3, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_24 = lean_apply_1(x_1, x_21);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set(x_25, 5, x_23);
x_26 = lean_st_ref_set(x_3, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadTraceCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadTraceCoreM___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadTraceCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadTraceCoreM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadTraceCoreM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadTraceCoreM___closed__1;
x_2 = l_Lean_Core_instMonadTraceCoreM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instMonadTraceCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadTraceCoreM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadTraceCoreM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 5);
x_11 = lean_ctor_get(x_6, 5);
lean_dec(x_11);
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_ctor_set(x_6, 5, x_10);
lean_ctor_set(x_6, 0, x_9);
x_13 = lean_st_ref_set(x_3, x_6, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 5);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 2);
x_24 = lean_ctor_get(x_6, 3);
x_25 = lean_ctor_get(x_6, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
lean_inc(x_21);
lean_inc(x_20);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_21);
x_27 = lean_st_ref_set(x_3, x_26, x_7);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_restore(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_ctor_set(x_6, 1, x_11);
x_12 = lean_st_ref_set(x_3, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_environment_main_module(x_17);
x_19 = l_Lean_addMacroScope(x_18, x_1, x_9);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_environment_main_module(x_22);
x_24 = l_Lean_addMacroScope(x_23, x_1, x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_ctor_get(x_6, 3);
x_30 = lean_ctor_get(x_6, 4);
x_31 = lean_ctor_get(x_6, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_27, x_32);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_31);
x_35 = lean_st_ref_set(x_3, x_34, x_7);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_3, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_environment_main_module(x_41);
x_43 = l_Lean_addMacroScope(x_42, x_1, x_27);
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_40;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_mkFreshUserName(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
x_8 = lean_apply_3(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_CoreM_run___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
x_8 = lean_apply_3(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_CoreM_run_x27___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_CoreM_toIO___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("internal exception #", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_io_get_num_heartbeats(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 8);
lean_dec(x_9);
lean_ctor_set(x_2, 8, x_6);
x_10 = lean_st_mk_ref(x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_apply_3(x_1, x_2, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_11);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MessageData_toString(x_26, x_25);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_13, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_24, 0);
lean_inc(x_41);
lean_dec(x_24);
x_42 = l_Nat_repr(x_41);
x_43 = l_Lean_Core_CoreM_toIO___rarg___closed__1;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_13, 0, x_45);
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_dec(x_13);
x_47 = lean_ctor_get(x_24, 0);
lean_inc(x_47);
lean_dec(x_24);
x_48 = l_Nat_repr(x_47);
x_49 = l_Lean_Core_CoreM_toIO___rarg___closed__1;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_ctor_get(x_2, 3);
x_57 = lean_ctor_get(x_2, 4);
x_58 = lean_ctor_get(x_2, 5);
x_59 = lean_ctor_get(x_2, 6);
x_60 = lean_ctor_get(x_2, 7);
x_61 = lean_ctor_get(x_2, 9);
x_62 = lean_ctor_get(x_2, 10);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_54);
lean_ctor_set(x_63, 2, x_55);
lean_ctor_set(x_63, 3, x_56);
lean_ctor_set(x_63, 4, x_57);
lean_ctor_set(x_63, 5, x_58);
lean_ctor_set(x_63, 6, x_59);
lean_ctor_set(x_63, 7, x_60);
lean_ctor_set(x_63, 8, x_6);
lean_ctor_set(x_63, 9, x_61);
lean_ctor_set(x_63, 10, x_62);
x_64 = lean_st_mk_ref(x_3, x_7);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_65);
x_67 = lean_apply_3(x_1, x_63, x_65, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_get(x_65, x_69);
lean_dec(x_65);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_71);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_65);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_dec(x_67);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_MessageData_toString(x_78, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_83, 0, x_80);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_82;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_87 = x_79;
} else {
 lean_dec_ref(x_79);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_ctor_get(x_67, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_90 = x_67;
} else {
 lean_dec_ref(x_67);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_76, 0);
lean_inc(x_91);
lean_dec(x_76);
x_92 = l_Nat_repr(x_91);
x_93 = l_Lean_Core_CoreM_toIO___rarg___closed__1;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_95, 0, x_94);
if (lean_is_scalar(x_90)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_90;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_89);
return x_96;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_CoreM_toIO___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Std_PersistentArray_forMAux___at_Lean_Core_instMetaEvalCoreM___spec__3(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_5, 5);
x_12 = l_Lean_MessageData_format(x_10, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_println___at_Lean_instEval__1___spec__1(x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_16;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_io_error_to_string(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_inc(x_11);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_io_error_to_string(x_27);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_inc(x_11);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_io_error_to_string(x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_11);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_12, 0, x_39);
return x_12;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
x_42 = lean_io_error_to_string(x_40);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_11);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_7);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forMAux___at_Lean_Core_instMetaEvalCoreM___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_6, x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__4(x_5, x_14, x_15, x_16, x_2, x_3, x_4);
lean_dec(x_5);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_array_get_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_19, x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__5(x_18, x_27, x_28, x_29, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_18);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forM___at_Lean_Core_instMetaEvalCoreM___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Std_PersistentArray_forMAux___at_Lean_Core_instMetaEvalCoreM___spec__3(x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_6);
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__5(x_10, x_17, x_18, x_19, x_2, x_3, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_10);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_23, x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__5(x_22, x_31, x_32, x_33, x_2, x_3, x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_22);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
return x_6;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Std_PersistentArray_forM___at_Lean_Core_instMetaEvalCoreM___spec__2(x_8, x_1, x_2, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__3;
x_2 = l_Lean_Core_instInhabitedState___closed__3;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<CoreM>", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_29 = l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__2;
x_30 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_3, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Core_getMaxHeartbeats(x_3);
x_33 = l_Lean_Core_State_nextMacroScope___default___closed__1;
x_34 = l_Lean_Core_State_ngen___default___closed__3;
x_35 = l_Lean_Core_State_traceState___default___closed__4;
x_36 = l_Lean_Core_instInhabitedCache___closed__1;
x_37 = l_Lean_Core_State_traceState___default___closed__3;
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
lean_ctor_set(x_38, 5, x_37);
x_39 = lean_io_get_num_heartbeats(x_6);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__3;
x_43 = l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__1;
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_box(0);
x_46 = lean_box(0);
x_47 = l_Lean_firstFrontendMacroScope;
lean_inc(x_3);
x_48 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_3);
lean_ctor_set(x_48, 3, x_44);
lean_ctor_set(x_48, 4, x_30);
lean_ctor_set(x_48, 5, x_45);
lean_ctor_set(x_48, 6, x_46);
lean_ctor_set(x_48, 7, x_31);
lean_ctor_set(x_48, 8, x_40);
lean_ctor_set(x_48, 9, x_32);
lean_ctor_set(x_48, 10, x_47);
x_49 = lean_st_mk_ref(x_38, x_41);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_50);
lean_inc(x_48);
x_52 = lean_apply_3(x_4, x_48, x_50, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(x_48, x_50, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_50, x_56);
lean_dec(x_50);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = 1;
x_62 = lean_box(x_61);
x_63 = lean_apply_5(x_1, x_60, x_3, x_53, x_62, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_ctor_get(x_55, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_dec(x_55);
x_7 = x_64;
x_8 = x_65;
goto block_28;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_3);
lean_dec(x_1);
x_66 = lean_ctor_get(x_52, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
lean_dec(x_52);
x_68 = l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(x_48, x_50, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_7 = x_66;
x_8 = x_69;
goto block_28;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_66);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_7 = x_70;
x_8 = x_71;
goto block_28;
}
}
block_28:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_MessageData_toString(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = l_Nat_repr(x_22);
x_24 = l_Lean_Core_CoreM_toIO___rarg___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMetaEvalCoreM___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMetaEvalCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMetaEvalCoreM___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__4(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Core_instMetaEvalCoreM___spec__5(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 7);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 10);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_10, x_11);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_4, 10);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 9);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 8);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 7);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 6);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 5);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 4);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 3);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 0);
lean_dec(x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_10, x_31);
lean_dec(x_10);
lean_ctor_set(x_4, 3, x_32);
x_33 = lean_apply_5(x_3, lean_box(0), x_1, x_4, x_5, x_6);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_10, x_34);
lean_dec(x_10);
x_36 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_8);
lean_ctor_set(x_36, 2, x_9);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_11);
lean_ctor_set(x_36, 5, x_12);
lean_ctor_set(x_36, 6, x_13);
lean_ctor_set(x_36, 7, x_14);
lean_ctor_set(x_36, 8, x_15);
lean_ctor_set(x_36, 9, x_16);
lean_ctor_set(x_36, 10, x_17);
x_37 = lean_apply_5(x_3, lean_box(0), x_1, x_36, x_5, x_6);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_38 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg(x_12, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___rarg___lambda__1), 6, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_apply_2(x_6, lean_box(0), x_5);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_8, lean_box(0));
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(deterministic) timeout at '", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', maximum number of heartbeats (", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(") has been reached (use 'set_option ", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" <num>' to set the limit)", 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_7 = 1;
x_8 = l_Lean_Name_toString(x_1, x_7);
x_9 = l_Lean_Core_throwMaxHeartbeat___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_Core_throwMaxHeartbeat___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_unsigned_to_nat(1000u);
x_14 = lean_nat_div(x_3, x_13);
x_15 = l_Nat_repr(x_14);
x_16 = lean_string_append(x_12, x_15);
lean_dec(x_15);
x_17 = l_Lean_Core_throwMaxHeartbeat___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Lean_Name_toString(x_2, x_7);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = l_Lean_Core_throwMaxHeartbeat___closed__4;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_ctor_get(x_4, 5);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_throwMaxHeartbeat(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_io_get_num_heartbeats(x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
x_15 = lean_nat_dec_lt(x_3, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_9);
x_17 = lean_box(0);
x_18 = l_Lean_Name_str___override(x_17, x_1);
x_19 = l_Lean_Core_throwMaxHeartbeat(x_18, x_2, x_3, x_4, x_5, x_12);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_4, 8);
x_23 = lean_nat_sub(x_20, x_22);
lean_dec(x_20);
x_24 = lean_nat_dec_lt(x_3, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = l_Lean_Name_str___override(x_27, x_1);
x_29 = l_Lean_Core_throwMaxHeartbeat(x_28, x_2, x_3, x_4, x_5, x_21);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_checkMaxHeartbeatsCore(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 9);
x_6 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__2;
x_7 = l_Lean_Core_checkMaxHeartbeatsCore(x_1, x_6, x_5, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkMaxHeartbeats(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_io_get_num_heartbeats(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 8);
lean_dec(x_9);
lean_ctor_set(x_2, 8, x_6);
x_10 = lean_apply_3(x_1, x_2, x_3, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_2, 4);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_ctor_get(x_2, 6);
x_18 = lean_ctor_get(x_2, 7);
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get(x_2, 10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_13);
lean_ctor_set(x_21, 3, x_14);
lean_ctor_set(x_21, 4, x_15);
lean_ctor_set(x_21, 5, x_16);
lean_ctor_set(x_21, 6, x_17);
lean_ctor_set(x_21, 7, x_18);
lean_ctor_set(x_21, 8, x_6);
lean_ctor_set(x_21, 9, x_19);
lean_ctor_set(x_21, 10, x_20);
x_22 = lean_apply_3(x_1, x_21, x_3, x_7);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_2(x_2, lean_box(0), x_1);
x_7 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___rarg___lambda__1), 5, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_apply_2(x_6, lean_box(0), x_5);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_8, lean_box(0));
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 5);
lean_dec(x_9);
lean_ctor_set(x_6, 5, x_1);
x_10 = lean_st_ref_set(x_3, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get(x_6, 3);
x_21 = lean_ctor_get(x_6, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_1);
x_23 = lean_st_ref_set(x_3, x_22, x_7);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_setMessageLog(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Core_State_traceState___default___closed__3;
x_5 = l_Lean_Core_setMessageLog(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_resetMessageLog(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 5);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 5);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_getMessageLog___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getMessageLog___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_getMessageLog(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 5);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 5);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_2, 6);
x_8 = lean_ctor_get(x_2, 7);
lean_inc(x_8);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_1, 4, x_10);
x_11 = lean_st_ref_take(x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 5);
x_16 = l_Std_PersistentArray_push___rarg(x_15, x_1);
lean_ctor_set(x_12, 5, x_16);
x_17 = lean_st_ref_set(x_3, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
x_27 = lean_ctor_get(x_12, 3);
x_28 = lean_ctor_get(x_12, 4);
x_29 = lean_ctor_get(x_12, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_30 = l_Std_PersistentArray_push___rarg(x_29, x_1);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_30);
x_32 = lean_st_ref_set(x_3, x_31, x_13);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ctor_get(x_1, 2);
x_40 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_41 = lean_ctor_get(x_1, 3);
x_42 = lean_ctor_get(x_1, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_43 = lean_ctor_get(x_2, 6);
x_44 = lean_ctor_get(x_2, 7);
lean_inc(x_44);
lean_inc(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_38);
lean_ctor_set(x_47, 2, x_39);
lean_ctor_set(x_47, 3, x_41);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*5, x_40);
x_48 = lean_st_ref_take(x_3, x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 5);
lean_inc(x_56);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 lean_ctor_release(x_49, 3);
 lean_ctor_release(x_49, 4);
 lean_ctor_release(x_49, 5);
 x_57 = x_49;
} else {
 lean_dec_ref(x_49);
 x_57 = lean_box(0);
}
x_58 = l_Std_PersistentArray_push___rarg(x_56, x_47);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 6, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_54);
lean_ctor_set(x_59, 4, x_55);
lean_ctor_set(x_59, 5, x_58);
x_60 = lean_st_ref_set(x_3, x_59, x_50);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lambda__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Core_instMonadLogCoreM___closed__1;
x_2 = l_Lean_Core_instMonadRefCoreM___closed__1;
x_3 = l_Lean_Core_instMonadLogCoreM___closed__2;
x_4 = l_Lean_Core_instMonadLogCoreM___closed__3;
x_5 = l_Lean_Core_instMonadLogCoreM___closed__4;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadLogCoreM___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadLogCoreM___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_nat_dec_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_9, lean_box(0), x_4);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_apply_1(x_3, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_catchInternalId___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_3(x_5, lean_box(0), x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_catchInternalId___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_catchInternalId___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_catchInternalId(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_catchInternalIds___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_List_elem___at_Lean_catchInternalIds___spec__1(x_7, x_2);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_9, lean_box(0), x_4);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_apply_1(x_3, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_3(x_5, lean_box(0), x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_catchInternalIds___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_catchInternalIds___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_catchInternalIds___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_catchInternalIds(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Exception_isMaxHeartbeat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(deterministic) timeout", 23);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_Exception_isMaxHeartbeat___closed__1;
x_6 = l_String_isPrefixOf(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_isMaxHeartbeat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_RecDepth(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ResolveName(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_RecDepth(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_InternalExceptionId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__1 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__1();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__1);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__2 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__2();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__2);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__3 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__3();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__3);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__4 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__4();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__4);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__5 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__5();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7____closed__5);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_7_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_maxHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_maxHeartbeats);
lean_dec_ref(res);
}l_Lean_Core_getMaxHeartbeats___closed__1 = _init_l_Lean_Core_getMaxHeartbeats___closed__1();
lean_mark_persistent(l_Lean_Core_getMaxHeartbeats___closed__1);
l_Lean_Core_Cache_instLevelType___default___closed__1 = _init_l_Lean_Core_Cache_instLevelType___default___closed__1();
lean_mark_persistent(l_Lean_Core_Cache_instLevelType___default___closed__1);
l_Lean_Core_Cache_instLevelType___default___closed__2 = _init_l_Lean_Core_Cache_instLevelType___default___closed__2();
lean_mark_persistent(l_Lean_Core_Cache_instLevelType___default___closed__2);
l_Lean_Core_Cache_instLevelType___default___closed__3 = _init_l_Lean_Core_Cache_instLevelType___default___closed__3();
lean_mark_persistent(l_Lean_Core_Cache_instLevelType___default___closed__3);
l_Lean_Core_Cache_instLevelType___default = _init_l_Lean_Core_Cache_instLevelType___default();
lean_mark_persistent(l_Lean_Core_Cache_instLevelType___default);
l_Lean_Core_Cache_instLevelValue___default = _init_l_Lean_Core_Cache_instLevelValue___default();
lean_mark_persistent(l_Lean_Core_Cache_instLevelValue___default);
l_Lean_Core_instInhabitedCache___closed__1 = _init_l_Lean_Core_instInhabitedCache___closed__1();
lean_mark_persistent(l_Lean_Core_instInhabitedCache___closed__1);
l_Lean_Core_instInhabitedCache = _init_l_Lean_Core_instInhabitedCache();
lean_mark_persistent(l_Lean_Core_instInhabitedCache);
l_Lean_Core_State_nextMacroScope___default___closed__1 = _init_l_Lean_Core_State_nextMacroScope___default___closed__1();
lean_mark_persistent(l_Lean_Core_State_nextMacroScope___default___closed__1);
l_Lean_Core_State_nextMacroScope___default = _init_l_Lean_Core_State_nextMacroScope___default();
lean_mark_persistent(l_Lean_Core_State_nextMacroScope___default);
l_Lean_Core_State_ngen___default___closed__1 = _init_l_Lean_Core_State_ngen___default___closed__1();
lean_mark_persistent(l_Lean_Core_State_ngen___default___closed__1);
l_Lean_Core_State_ngen___default___closed__2 = _init_l_Lean_Core_State_ngen___default___closed__2();
lean_mark_persistent(l_Lean_Core_State_ngen___default___closed__2);
l_Lean_Core_State_ngen___default___closed__3 = _init_l_Lean_Core_State_ngen___default___closed__3();
lean_mark_persistent(l_Lean_Core_State_ngen___default___closed__3);
l_Lean_Core_State_ngen___default = _init_l_Lean_Core_State_ngen___default();
lean_mark_persistent(l_Lean_Core_State_ngen___default);
l_Lean_Core_State_traceState___default___closed__1 = _init_l_Lean_Core_State_traceState___default___closed__1();
lean_mark_persistent(l_Lean_Core_State_traceState___default___closed__1);
l_Lean_Core_State_traceState___default___closed__2 = _init_l_Lean_Core_State_traceState___default___closed__2();
lean_mark_persistent(l_Lean_Core_State_traceState___default___closed__2);
l_Lean_Core_State_traceState___default___closed__3 = _init_l_Lean_Core_State_traceState___default___closed__3();
lean_mark_persistent(l_Lean_Core_State_traceState___default___closed__3);
l_Lean_Core_State_traceState___default___closed__4 = _init_l_Lean_Core_State_traceState___default___closed__4();
lean_mark_persistent(l_Lean_Core_State_traceState___default___closed__4);
l_Lean_Core_State_traceState___default = _init_l_Lean_Core_State_traceState___default();
lean_mark_persistent(l_Lean_Core_State_traceState___default);
l_Lean_Core_State_cache___default = _init_l_Lean_Core_State_cache___default();
lean_mark_persistent(l_Lean_Core_State_cache___default);
l_Lean_Core_State_messages___default = _init_l_Lean_Core_State_messages___default();
lean_mark_persistent(l_Lean_Core_State_messages___default);
l_Lean_Core_instInhabitedState___closed__1 = _init_l_Lean_Core_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__1);
l_Lean_Core_instInhabitedState___closed__2 = _init_l_Lean_Core_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__2);
l_Lean_Core_instInhabitedState___closed__3 = _init_l_Lean_Core_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__3);
l_Lean_Core_instInhabitedState___closed__4 = _init_l_Lean_Core_instInhabitedState___closed__4();
l_Lean_Core_instInhabitedState___closed__5 = _init_l_Lean_Core_instInhabitedState___closed__5();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__5);
l_Lean_Core_instInhabitedState___closed__6 = _init_l_Lean_Core_instInhabitedState___closed__6();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__6);
l_Lean_Core_instInhabitedState___closed__7 = _init_l_Lean_Core_instInhabitedState___closed__7();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__7);
l_Lean_Core_instInhabitedState___closed__8 = _init_l_Lean_Core_instInhabitedState___closed__8();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__8);
l_Lean_Core_instInhabitedState___closed__9 = _init_l_Lean_Core_instInhabitedState___closed__9();
l_Lean_Core_instInhabitedState___closed__10 = _init_l_Lean_Core_instInhabitedState___closed__10();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__10);
l_Lean_Core_instInhabitedState___closed__11 = _init_l_Lean_Core_instInhabitedState___closed__11();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__11);
l_Lean_Core_instInhabitedState___closed__12 = _init_l_Lean_Core_instInhabitedState___closed__12();
lean_mark_persistent(l_Lean_Core_instInhabitedState___closed__12);
l_Lean_Core_instInhabitedState = _init_l_Lean_Core_instInhabitedState();
lean_mark_persistent(l_Lean_Core_instInhabitedState);
l_Lean_Core_Context_options___default = _init_l_Lean_Core_Context_options___default();
lean_mark_persistent(l_Lean_Core_Context_options___default);
l_Lean_Core_Context_currRecDepth___default = _init_l_Lean_Core_Context_currRecDepth___default();
lean_mark_persistent(l_Lean_Core_Context_currRecDepth___default);
l_Lean_Core_Context_maxRecDepth___default = _init_l_Lean_Core_Context_maxRecDepth___default();
lean_mark_persistent(l_Lean_Core_Context_maxRecDepth___default);
l_Lean_Core_Context_ref___default = _init_l_Lean_Core_Context_ref___default();
lean_mark_persistent(l_Lean_Core_Context_ref___default);
l_Lean_Core_Context_currNamespace___default = _init_l_Lean_Core_Context_currNamespace___default();
lean_mark_persistent(l_Lean_Core_Context_currNamespace___default);
l_Lean_Core_Context_openDecls___default = _init_l_Lean_Core_Context_openDecls___default();
lean_mark_persistent(l_Lean_Core_Context_openDecls___default);
l_Lean_Core_Context_initHeartbeats___default = _init_l_Lean_Core_Context_initHeartbeats___default();
lean_mark_persistent(l_Lean_Core_Context_initHeartbeats___default);
l_Lean_Core_Context_currMacroScope___default = _init_l_Lean_Core_Context_currMacroScope___default();
lean_mark_persistent(l_Lean_Core_Context_currMacroScope___default);
l_Lean_Core_instMonadCoreM___closed__1 = _init_l_Lean_Core_instMonadCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__1);
l_Lean_Core_instMonadCoreM___closed__2 = _init_l_Lean_Core_instMonadCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__2);
l_Lean_Core_instMonadCoreM___closed__3 = _init_l_Lean_Core_instMonadCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__3);
l_Lean_Core_instMonadCoreM___closed__4 = _init_l_Lean_Core_instMonadCoreM___closed__4();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__4);
l_Lean_Core_instMonadCoreM___closed__5 = _init_l_Lean_Core_instMonadCoreM___closed__5();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__5);
l_Lean_Core_instMonadCoreM___closed__6 = _init_l_Lean_Core_instMonadCoreM___closed__6();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__6);
l_Lean_Core_instMonadCoreM = _init_l_Lean_Core_instMonadCoreM();
lean_mark_persistent(l_Lean_Core_instMonadCoreM);
l_Lean_Core_instInhabitedCoreM___rarg___closed__1 = _init_l_Lean_Core_instInhabitedCoreM___rarg___closed__1();
lean_mark_persistent(l_Lean_Core_instInhabitedCoreM___rarg___closed__1);
l_Lean_Core_instInhabitedCoreM___rarg___closed__2 = _init_l_Lean_Core_instInhabitedCoreM___rarg___closed__2();
lean_mark_persistent(l_Lean_Core_instInhabitedCoreM___rarg___closed__2);
l_Lean_Core_instMonadRefCoreM___closed__1 = _init_l_Lean_Core_instMonadRefCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadRefCoreM___closed__1);
l_Lean_Core_instMonadRefCoreM___closed__2 = _init_l_Lean_Core_instMonadRefCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadRefCoreM___closed__2);
l_Lean_Core_instMonadRefCoreM___closed__3 = _init_l_Lean_Core_instMonadRefCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadRefCoreM___closed__3);
l_Lean_Core_instMonadRefCoreM = _init_l_Lean_Core_instMonadRefCoreM();
lean_mark_persistent(l_Lean_Core_instMonadRefCoreM);
l_Lean_Core_instMonadEnvCoreM___closed__1 = _init_l_Lean_Core_instMonadEnvCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadEnvCoreM___closed__1);
l_Lean_Core_instMonadEnvCoreM___closed__2 = _init_l_Lean_Core_instMonadEnvCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadEnvCoreM___closed__2);
l_Lean_Core_instMonadEnvCoreM___closed__3 = _init_l_Lean_Core_instMonadEnvCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadEnvCoreM___closed__3);
l_Lean_Core_instMonadEnvCoreM = _init_l_Lean_Core_instMonadEnvCoreM();
lean_mark_persistent(l_Lean_Core_instMonadEnvCoreM);
l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1 = _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1);
l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2 = _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2);
l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3 = _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3);
l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4 = _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4);
l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5 = _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5);
l_Lean_Core_instAddMessageContextCoreM___closed__1 = _init_l_Lean_Core_instAddMessageContextCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instAddMessageContextCoreM___closed__1);
l_Lean_Core_instAddMessageContextCoreM = _init_l_Lean_Core_instAddMessageContextCoreM();
lean_mark_persistent(l_Lean_Core_instAddMessageContextCoreM);
l_Lean_Core_instMonadNameGeneratorCoreM___closed__1 = _init_l_Lean_Core_instMonadNameGeneratorCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadNameGeneratorCoreM___closed__1);
l_Lean_Core_instMonadNameGeneratorCoreM___closed__2 = _init_l_Lean_Core_instMonadNameGeneratorCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadNameGeneratorCoreM___closed__2);
l_Lean_Core_instMonadNameGeneratorCoreM___closed__3 = _init_l_Lean_Core_instMonadNameGeneratorCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadNameGeneratorCoreM___closed__3);
l_Lean_Core_instMonadNameGeneratorCoreM = _init_l_Lean_Core_instMonadNameGeneratorCoreM();
lean_mark_persistent(l_Lean_Core_instMonadNameGeneratorCoreM);
l_Lean_Core_instMonadRecDepthCoreM___closed__1 = _init_l_Lean_Core_instMonadRecDepthCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadRecDepthCoreM___closed__1);
l_Lean_Core_instMonadRecDepthCoreM___closed__2 = _init_l_Lean_Core_instMonadRecDepthCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadRecDepthCoreM___closed__2);
l_Lean_Core_instMonadRecDepthCoreM___closed__3 = _init_l_Lean_Core_instMonadRecDepthCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadRecDepthCoreM___closed__3);
l_Lean_Core_instMonadRecDepthCoreM___closed__4 = _init_l_Lean_Core_instMonadRecDepthCoreM___closed__4();
lean_mark_persistent(l_Lean_Core_instMonadRecDepthCoreM___closed__4);
l_Lean_Core_instMonadRecDepthCoreM = _init_l_Lean_Core_instMonadRecDepthCoreM();
lean_mark_persistent(l_Lean_Core_instMonadRecDepthCoreM);
l_Lean_Core_instMonadResolveNameCoreM___closed__1 = _init_l_Lean_Core_instMonadResolveNameCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadResolveNameCoreM___closed__1);
l_Lean_Core_instMonadResolveNameCoreM___closed__2 = _init_l_Lean_Core_instMonadResolveNameCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadResolveNameCoreM___closed__2);
l_Lean_Core_instMonadResolveNameCoreM___closed__3 = _init_l_Lean_Core_instMonadResolveNameCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadResolveNameCoreM___closed__3);
l_Lean_Core_instMonadResolveNameCoreM = _init_l_Lean_Core_instMonadResolveNameCoreM();
lean_mark_persistent(l_Lean_Core_instMonadResolveNameCoreM);
l_Lean_Core_instMonadQuotationCoreM___closed__1 = _init_l_Lean_Core_instMonadQuotationCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadQuotationCoreM___closed__1);
l_Lean_Core_instMonadQuotationCoreM___closed__2 = _init_l_Lean_Core_instMonadQuotationCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadQuotationCoreM___closed__2);
l_Lean_Core_instMonadQuotationCoreM___closed__3 = _init_l_Lean_Core_instMonadQuotationCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadQuotationCoreM___closed__3);
l_Lean_Core_instMonadQuotationCoreM___closed__4 = _init_l_Lean_Core_instMonadQuotationCoreM___closed__4();
lean_mark_persistent(l_Lean_Core_instMonadQuotationCoreM___closed__4);
l_Lean_Core_instMonadQuotationCoreM = _init_l_Lean_Core_instMonadQuotationCoreM();
lean_mark_persistent(l_Lean_Core_instMonadQuotationCoreM);
l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1();
l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3);
l_Lean_Core_instMonadTraceCoreM___closed__1 = _init_l_Lean_Core_instMonadTraceCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM___closed__1);
l_Lean_Core_instMonadTraceCoreM___closed__2 = _init_l_Lean_Core_instMonadTraceCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM___closed__2);
l_Lean_Core_instMonadTraceCoreM___closed__3 = _init_l_Lean_Core_instMonadTraceCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM___closed__3);
l_Lean_Core_instMonadTraceCoreM = _init_l_Lean_Core_instMonadTraceCoreM();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM);
l_Lean_Core_CoreM_toIO___rarg___closed__1 = _init_l_Lean_Core_CoreM_toIO___rarg___closed__1();
lean_mark_persistent(l_Lean_Core_CoreM_toIO___rarg___closed__1);
l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__1 = _init_l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__1);
l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__2 = _init_l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__2);
l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__3 = _init_l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Core_instMetaEvalCoreM___rarg___lambda__1___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2);
l_Lean_Core_throwMaxHeartbeat___closed__1 = _init_l_Lean_Core_throwMaxHeartbeat___closed__1();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__1);
l_Lean_Core_throwMaxHeartbeat___closed__2 = _init_l_Lean_Core_throwMaxHeartbeat___closed__2();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__2);
l_Lean_Core_throwMaxHeartbeat___closed__3 = _init_l_Lean_Core_throwMaxHeartbeat___closed__3();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__3);
l_Lean_Core_throwMaxHeartbeat___closed__4 = _init_l_Lean_Core_throwMaxHeartbeat___closed__4();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__4);
l_Lean_Core_instMonadLogCoreM___closed__1 = _init_l_Lean_Core_instMonadLogCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___closed__1);
l_Lean_Core_instMonadLogCoreM___closed__2 = _init_l_Lean_Core_instMonadLogCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___closed__2);
l_Lean_Core_instMonadLogCoreM___closed__3 = _init_l_Lean_Core_instMonadLogCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___closed__3);
l_Lean_Core_instMonadLogCoreM___closed__4 = _init_l_Lean_Core_instMonadLogCoreM___closed__4();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___closed__4);
l_Lean_Core_instMonadLogCoreM___closed__5 = _init_l_Lean_Core_instMonadLogCoreM___closed__5();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___closed__5);
l_Lean_Core_instMonadLogCoreM = _init_l_Lean_Core_instMonadLogCoreM();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM);
l_Lean_Exception_isMaxHeartbeat___closed__1 = _init_l_Lean_Exception_isMaxHeartbeat___closed__1();
lean_mark_persistent(l_Lean_Exception_isMaxHeartbeat___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
