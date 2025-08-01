// Lean compiler output
// Module: Lean.CoreM
// Imports: Lean.Util.RecDepth Lean.Util.Trace Lean.Log Lean.ResolveName Lean.Elab.InfoTree.Types Lean.MonadEnv Lean.Elab.Exception Lean.Language.Basic
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
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_193_;
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_;
static lean_object* l___auto___closed__19____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3;
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__2;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4808_;
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__1;
static lean_object* l_Lean_Core_instMonadCoreM___closed__1;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_154_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls___closed__3;
static lean_object* l___auto___closed__18____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__0;
static lean_object* l___auto___closed__23____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_traceBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_41_;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_81_;
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__1;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0(lean_object*);
lean_object* l_Lean_ConstantVal_instantiateTypeLevelParams(lean_object*, lean_object*);
static double l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_115_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_4808_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
static double l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__6;
lean_object* l_Lean_Environment_constants(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__3;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0;
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_6_;
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*, lean_object*);
static lean_object* l___auto___closed__37____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_81_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
double lean_float_div(double, double);
lean_object* lean_io_get_tid(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_DeclNameGenerator_mkUniqueName_isConflict(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDeclsImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Core_instantiateValueLevelParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_81_;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_927_;
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__38____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_186_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instAddMessageContextCoreM___closed__0;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__7____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_115_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_saveState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isRealizing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM;
static lean_object* l___auto___closed__10____x40_Lean_CoreM___hyg_4846_;
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__2;
static lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__3;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___auto___closed__27____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7148_;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_41__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_initFn____x40_Lean_CoreM___hyg_7148_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_927_;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__1____x40_Lean_CoreM___hyg_4846_;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_41_;
static lean_object* l___auto___closed__35____x40_Lean_CoreM___hyg_4846_;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16;
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM;
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_154_;
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6_(lean_object*);
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_catchInternalIds___redArg___closed__0;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_Core_instAddMessageContextCoreM___closed__1;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_41_;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18____x40_Lean_CoreM___hyg_927_;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_81_(lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs___boxed(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_compileDecls___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__6____x40_Lean_CoreM___hyg_4846_;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__0;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_193_;
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__6;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_154_;
static lean_object* l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4808_;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__10;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__12;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__14;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30(lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__2;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__16____x40_Lean_CoreM___hyg_4846_;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(size_t, size_t, lean_object*);
static lean_object* l_Lean_mkArrow___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCache___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_traceBlock___redArg___closed__1;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__3;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLiftIOCoreM___closed__0;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_CoreM___hyg_4846_;
static lean_object* l_Lean_Core_instInhabitedCache___closed__1;
static lean_object* l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3762_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_927_;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_CancelToken_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__33____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_81_;
static lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__3;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_115_;
static lean_object* l___auto___closed__2____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25;
lean_object* lean_lcnf_compile_decls(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__12;
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_curr(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_927_;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static size_t l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__2;
static lean_object* l___auto___closed__26____x40_Lean_CoreM___hyg_4846_;
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_IO_addHeartbeats(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__4;
static lean_object* l___auto___closed__5____x40_Lean_CoreM___hyg_4846_;
lean_object* l_instDecidableEqPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__20____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__4;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__9;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4808_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_41_;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___redArg(lean_object*, lean_object*);
static uint8_t l_Lean_ImportM_runCoreM___redArg___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_async;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3;
static uint64_t l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instantiateValueLevelParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_getMaxHeartbeats___closed__0;
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__22____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__8(lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__14;
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__13;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__0;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionCoreM;
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__12____x40_Lean_CoreM___hyg_4846_;
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___closed__1;
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_193_(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__2;
static lean_object* l___auto___closed__14____x40_Lean_CoreM___hyg_4846_;
static lean_object* l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4808_;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3762_;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_curr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_115_;
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__29____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkChild(lean_object*);
static lean_object* l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4808_;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_DeclNameGenerator_mkUniqueName_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_193_;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_compileDecls_doCompile_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDiag___boxed(lean_object*);
extern lean_object* l_Lean_warningAsError;
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__9;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17;
lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams_x21(lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2___redArg(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg(lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__0;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__1;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_154_;
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_6_;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_traceBlock___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_PromiseCheckedResult_commitChecked(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_154_(lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
static lean_object* l___auto___closed__4____x40_Lean_CoreM___hyg_4846_;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__6;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l___auto___closed__32____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__7;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_927_;
static lean_object* l_Lean_useDiagnosticMsg___lam__0___closed__1;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__8;
static lean_object* l___auto___closed__15____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashablePos___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__3;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28;
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19;
static lean_object* l_Lean_instMonadExceptOfExceptionCoreM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_193_;
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__1;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__7;
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_154_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__28____x40_Lean_CoreM___hyg_4846_;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_193_;
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__25____x40_Lean_CoreM___hyg_4846_;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3762_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_115_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__0____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3762_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclNameGenerator;
static lean_object* l___auto___closed__31____x40_Lean_CoreM___hyg_4846_;
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls___closed__0;
LEAN_EXPORT lean_object* l___auto____x40_Lean_CoreM___hyg_4987_;
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__7;
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCache___closed__2;
LEAN_EXPORT lean_object* l_Lean_compileDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7148_;
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5;
static lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Core_instMonadLogCoreM___lam__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueNat;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___auto___closed__36____x40_Lean_CoreM___hyg_4846_;
lean_object* l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_29____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3762_;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instantiateValueLevelParams___closed__1;
static lean_object* l_Lean_instMonadRuntimeExceptionCoreM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_promiseChecked(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1;
static lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls___closed__1;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__0;
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3762_;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_41_(lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__9____x40_Lean_CoreM___hyg_4846_;
static lean_object* l___auto___closed__3____x40_Lean_CoreM___hyg_4846_;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_6_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__21____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_isConflict___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__8;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5;
static lean_object* l___auto___closed__11____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_mkArrow___redArg___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2;
static lean_object* l___auto___closed__13____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7148_;
LEAN_EXPORT lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__2;
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_compileDecls_doCompile_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_41_;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7148_;
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__2;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_stderrAsMessages;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_41__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_traceBlock___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_diagnostics_threshold;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn____x40_Lean_CoreM___hyg_927_(lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isRuntime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__10;
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__11;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrowN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_927_;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__39____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__8;
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__1;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_927_;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9;
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwInterruptException___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
static lean_object* l_Lean_useDiagnosticMsg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l___auto___closed__24____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__0;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_6_;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_inServer;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4808_;
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instAddMessageContextCoreM;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__10;
static lean_object* l___auto___closed__17____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_debug_moduleNameAtTimeout;
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__3;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_115_;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_next(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__11;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCache;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15____x40_Lean_CoreM___hyg_927_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_81_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__4;
LEAN_EXPORT uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__0;
static lean_object* l___auto___closed__8____x40_Lean_CoreM___hyg_4846_;
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instAddMessageContextCoreM___closed__2;
static lean_object* l_Lean_instInhabitedDeclNameGenerator___closed__0;
lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3762_;
static lean_object* l___auto___closed__30____x40_Lean_CoreM___hyg_4846_;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_maxHeartbeats;
LEAN_EXPORT lean_object* l_Lean_internal_cmdlineSnapshots;
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_ofPrefix(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3;
lean_object* l_Lean_MessageLog_markAllReported(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7148_;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getDiag(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_193_;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__0;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_CoreM_toIO___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__1___boxed(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13;
static lean_object* l___auto___closed__34____x40_Lean_CoreM___hyg_4846_;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__12;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__3;
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24;
static lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7148_;
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_inc(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diagnostics", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("collect diagnostic information", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_6_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_;
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_;
x_2 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_6_;
x_3 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_6_;
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_6_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_41__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_41_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("threshold", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_41_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_41_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_41_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only diagnostic counters above this threshold are reported by the definitional equality", 87, 87);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_41_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_41_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_;
x_3 = lean_unsigned_to_nat(20u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_41_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_41_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_41_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_41_;
x_3 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_41_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_41_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_41__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_41__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_41__spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_81_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxHeartbeats", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_81_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_81_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_81_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum amount of heartbeats per command. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit", 126, 126);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_81_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_81_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_3 = lean_unsigned_to_nat(200000u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_81_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_81_;
x_2 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_81_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_81_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_81_;
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_81_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_41__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_115_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("async", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_115_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_115_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_115_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("perform elaboration using multiple threads where possible\n\nThis option defaults to `false` but (when not explicitly set) is overridden to `true` in the Lean language server and cmdline. Metaprogramming users driving elaboration directly via e.g. `Lean.Elab.Command.elabCommandTopLevel` can opt into asynchronous elaboration by setting this option but then are responsible for processing messages and other data not only in the resulting command state but also from async tasks in `Lean.Command.Context.snap\?` and `Lean.Command.State.snapshotTasks`.", 548, 548);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_115_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_115_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_115_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_115_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_115_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_115_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_115_;
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_115_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_154_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inServer", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_154_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_154_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_154_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true if elaboration is being run inside the Lean language server\n\nThis option is set by the file worker and should not be modified otherwise.", 141, 141);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_154_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_154_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_154_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_154_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_154_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_154_;
x_3 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_154_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_154_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_193_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_193_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cmdlineSnapshots", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_193_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_193_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_193_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_193_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduce information stored in snapshots to the minimum necessary for the cmdline driver: diagnostics per command and final full snapshot", 135, 135);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_193_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_193_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_193_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_193_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_193_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_193_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_193_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_193_;
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_193_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(invalid MessageData.lazy, missing context)", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg___lam__0___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_useDiagnosticMsg___lam__0___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Additional diagnostic information may be available using the `set_option ", 73, 73);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" true` command.", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg___lam__2___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_5 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = l_Lean_useDiagnosticMsg___lam__2___closed__1;
x_10 = 1;
x_11 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_7, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
x_13 = l_Lean_useDiagnosticMsg___lam__2___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = l_Lean_MessageData_hint_x27(x_16);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = l_Lean_useDiagnosticMsg___lam__2___closed__1;
x_20 = 1;
x_21 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_18, x_20);
x_22 = lean_string_append(x_19, x_21);
lean_dec_ref(x_21);
x_23 = l_Lean_useDiagnosticMsg___lam__2___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = l_Lean_MessageData_hint_x27(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_useDiagnosticMsg___lam__2___closed__4;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
return x_30;
}
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__1___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__2___boxed), 2, 0);
x_4 = l_Lean_MessageData_lazy(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lam__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_useDiagnosticMsg___lam__1(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lam__2(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclNameGenerator___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclNameGenerator() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedDeclNameGenerator___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_ofPrefix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_next(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_8);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Lean_DeclNameGenerator_mkUniqueName_isConflict(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_9 = 0;
lean_inc_ref(x_1);
x_10 = l_Lean_Environment_setExporting(x_1, x_9);
x_11 = l_Lean_Environment_containsOnBranch(x_10, x_2);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isPrivateName(x_2);
if (x_12 == 0)
{
x_3 = x_12;
goto block_8;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_1);
x_13 = l_Lean_Environment_setExporting(x_1, x_11);
lean_inc(x_2);
x_14 = l_Lean_privateToUserName(x_2);
x_15 = l_Lean_Environment_containsOnBranch(x_13, x_14);
lean_dec(x_14);
x_3 = x_15;
goto block_8;
}
}
else
{
x_3 = x_11;
goto block_8;
}
block_8:
{
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_isPrivateName(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc_ref(x_1);
x_5 = l_Lean_Environment_setExporting(x_1, x_3);
x_6 = l_Lean_mkPrivateName(x_1, x_2);
lean_dec_ref(x_1);
x_7 = l_Lean_Environment_containsOnBranch(x_5, x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_isConflict___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_DeclNameGenerator_mkUniqueName_isConflict(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_name_append_index_after(x_4, x_8);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_mk(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = 0;
x_9 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(x_3, x_7, x_8, x_1);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_curr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Environment_header(x_1);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 4);
lean_dec_ref(x_4);
x_6 = l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs(x_2);
x_7 = l_List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0(x_3, x_6);
if (x_5 == 0)
{
goto block_10;
}
else
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_11 == 0)
{
goto block_10;
}
else
{
return x_7;
}
}
block_10:
{
if (x_5 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Lean_isPrivateName(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_mkPrivateName(x_1, x_7);
return x_9;
}
else
{
return x_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_curr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_DeclNameGenerator_mkUniqueName_curr(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_DeclNameGenerator_mkUniqueName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
x_4 = l_Lean_DeclNameGenerator_mkUniqueName_curr(x_1, x_3, x_2);
lean_inc_ref(x_1);
x_5 = l_Lean_DeclNameGenerator_mkUniqueName_isConflict(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_DeclNameGenerator_next(x_3);
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_11; uint8_t x_14; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_14 = l_Lean_Name_hasMacroScopes(x_4);
if (x_14 == 0)
{
x_11 = x_14;
goto block_13;
}
else
{
uint8_t x_15; 
x_15 = l_Lean_Name_hasMacroScopes(x_3);
x_11 = x_15;
goto block_13;
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Name_append(x_4, x_5);
lean_inc(x_6);
lean_inc_ref(x_1);
x_7 = l_Lean_Loop_forIn_loop___at___Lean_DeclNameGenerator_mkUniqueName_spec__0(x_1, x_6, x_2);
x_8 = l_Lean_DeclNameGenerator_mkUniqueName_curr(x_1, x_7, x_6);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_13:
{
if (x_11 == 0)
{
x_5 = x_3;
goto block_10;
}
else
{
lean_object* x_12; 
x_12 = lean_erase_macro_scopes(x_3);
x_5 = x_12;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkChild(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_inc(x_3);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
x_8 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_13);
lean_inc(x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_inc(x_11);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_2(x_1, lean_box(0), x_4);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_apply_2(x_1, lean_box(0), x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_DeclNameGenerator_mkUniqueName(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_mkAuxDeclName___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_8);
x_11 = lean_apply_1(x_4, x_9);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_mkAuxDeclName___redArg___lam__1), 6, 5);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_5);
lean_inc_ref(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_mkAuxDeclName___redArg___lam__2), 6, 5);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_8);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkAuxDeclName___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkAuxDeclName___redArg___lam__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_name_eq(x_10, x_1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
lean_inc_ref(x_3);
x_17 = lean_apply_1(x_3, x_16);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_5);
x_19 = lean_apply_1(x_3, x_9);
x_20 = lean_alloc_closure((void*)(l_Lean_withDeclNameForAuxNaming___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_18, x_20);
x_22 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_7, x_21);
return x_22;
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_withDeclNameForAuxNaming___redArg___lam__0___boxed), 1, 0);
lean_inc(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_withDeclNameForAuxNaming___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_5);
lean_inc_ref(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_withDeclNameForAuxNaming___redArg___lam__3___boxed), 9, 8);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_9);
lean_closure_set(x_12, 3, x_7);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_2);
lean_closure_set(x_12, 6, x_10);
lean_closure_set(x_12, 7, x_5);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withDeclNameForAuxNaming___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_withDeclNameForAuxNaming___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withDeclNameForAuxNaming___redArg___lam__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withDeclNameForAuxNaming___redArg___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withDeclNameForAuxNaming___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Kernel", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_927_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_927_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CoreM", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Core", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19____x40_Lean_CoreM___hyg_927_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(927u);
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn____x40_Lean_CoreM___hyg_927_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_927_;
x_3 = 0;
x_4 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19____x40_Lean_CoreM___hyg_927_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
static lean_object* _init_l_Lean_Core_getMaxHeartbeats___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxHeartbeats;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Core_getMaxHeartbeats___closed__0;
x_3 = l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(x_1, x_2);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
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
static lean_object* _init_l_Lean_Core_instInhabitedCache___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instInhabitedCache___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instInhabitedCache___closed__1;
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
x_1 = l_Lean_Core_instInhabitedCache___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
x_8 = lean_apply_3(x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_apply_4(x_4, x_9, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
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
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__1;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
lean_inc_ref(x_6);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_13, 0, x_6);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_17, 0, x_8);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_18, 0, x_7);
lean_ctor_set(x_3, 4, x_16);
lean_ctor_set(x_3, 3, x_17);
lean_ctor_set(x_3, 2, x_18);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_23 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
lean_inc_ref(x_19);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_25, 0, x_19);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_22);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_21);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_30, 0, x_20);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_32, 3);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_32, 4);
lean_inc_ref(x_36);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_37 = x_32;
} else {
 lean_dec_ref(x_32);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_39 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
lean_inc_ref(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
if (lean_is_scalar(x_37)) {
 x_46 = lean_alloc_ctor(0, 5, 0);
} else {
 x_46 = x_37;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 4, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instMonadCoreM___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCoreM___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCoreM___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instInhabitedCoreM___lam__0___closed__0;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Core_instInhabitedCoreM___lam__0___closed__1;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instInhabitedCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_21 = lean_ctor_get(x_4, 11);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_23 = lean_ctor_get(x_4, 12);
lean_inc(x_23);
lean_inc(x_21);
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
x_24 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
lean_ctor_set(x_24, 5, x_2);
lean_ctor_set(x_24, 6, x_15);
lean_ctor_set(x_24, 7, x_16);
lean_ctor_set(x_24, 8, x_17);
lean_ctor_set(x_24, 9, x_18);
lean_ctor_set(x_24, 10, x_19);
lean_ctor_set(x_24, 11, x_21);
lean_ctor_set(x_24, 12, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*13, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*13 + 1, x_22);
x_25 = lean_apply_3(x_3, x_24, x_5, x_6);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadRefCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRefCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRefCoreM___lam__1), 6, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRefCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc_ref(x_7);
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
lean_inc_ref(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 5);
lean_dec(x_10);
x_11 = lean_apply_1(x_1, x_9);
x_12 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_6, 5, x_12);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_28 = lean_apply_1(x_1, x_20);
x_29 = l_Lean_Core_instInhabitedCache___closed__2;
x_30 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set(x_30, 6, x_25);
lean_ctor_set(x_30, 7, x_26);
lean_ctor_set(x_30, 8, x_27);
x_31 = lean_st_ref_set(x_3, x_30, x_7);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadEnvCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadEnvCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadEnvCoreM___lam__1___boxed), 4, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadEnvCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadEnvCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Core_instMonadOptionsCoreM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadOptionsCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_76; uint8_t x_78; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 11);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*13 + 1);
x_24 = lean_ctor_get(x_6, 12);
lean_inc_ref(x_24);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 lean_ctor_release(x_6, 10);
 lean_ctor_release(x_6, 11);
 lean_ctor_release(x_6, 12);
 x_25 = x_6;
} else {
 lean_dec_ref(x_6);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_26);
lean_dec(x_10);
x_27 = lean_apply_1(x_4, x_14);
x_28 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_29 = l_Lean_Option_get___redArg(x_1, x_27, x_28);
x_78 = l_Lean_Kernel_isDiagnosticsEnabled(x_26);
lean_dec_ref(x_26);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = lean_unbox(x_29);
if (x_79 == 0)
{
x_30 = x_12;
x_31 = x_13;
x_32 = x_15;
x_33 = x_16;
x_34 = x_17;
x_35 = x_18;
x_36 = x_19;
x_37 = x_20;
x_38 = x_21;
x_39 = x_22;
x_40 = x_23;
x_41 = x_24;
x_42 = x_7;
x_43 = x_11;
goto block_49;
}
else
{
x_76 = x_78;
goto block_77;
}
}
else
{
uint8_t x_80; 
x_80 = lean_unbox(x_29);
if (x_80 == 0)
{
goto block_75;
}
else
{
x_76 = x_78;
goto block_77;
}
}
block_49:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_45 = l_Lean_Option_get___redArg(x_2, x_27, x_44);
if (lean_is_scalar(x_25)) {
 x_46 = lean_alloc_ctor(0, 13, 2);
} else {
 x_46 = x_25;
}
lean_ctor_set(x_46, 0, x_30);
lean_ctor_set(x_46, 1, x_31);
lean_ctor_set(x_46, 2, x_27);
lean_ctor_set(x_46, 3, x_32);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_33);
lean_ctor_set(x_46, 6, x_34);
lean_ctor_set(x_46, 7, x_35);
lean_ctor_set(x_46, 8, x_36);
lean_ctor_set(x_46, 9, x_37);
lean_ctor_set(x_46, 10, x_38);
lean_ctor_set(x_46, 11, x_39);
lean_ctor_set(x_46, 12, x_41);
x_47 = lean_unbox(x_29);
lean_dec(x_29);
lean_ctor_set_uint8(x_46, sizeof(void*)*13, x_47);
lean_ctor_set_uint8(x_46, sizeof(void*)*13 + 1, x_40);
x_48 = lean_apply_3(x_5, x_46, x_42, x_43);
return x_48;
}
block_75:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_st_ref_take(x_7, x_11);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 5);
lean_dec(x_55);
x_56 = lean_unbox(x_29);
x_57 = l_Lean_Kernel_enableDiag(x_54, x_56);
x_58 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_51, 5, x_58);
lean_ctor_set(x_51, 0, x_57);
x_59 = lean_st_ref_set(x_7, x_51, x_52);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec_ref(x_59);
x_30 = x_12;
x_31 = x_13;
x_32 = x_15;
x_33 = x_16;
x_34 = x_17;
x_35 = x_18;
x_36 = x_19;
x_37 = x_20;
x_38 = x_21;
x_39 = x_22;
x_40 = x_23;
x_41 = x_24;
x_42 = x_7;
x_43 = x_60;
goto block_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 1);
x_63 = lean_ctor_get(x_51, 2);
x_64 = lean_ctor_get(x_51, 3);
x_65 = lean_ctor_get(x_51, 4);
x_66 = lean_ctor_get(x_51, 6);
x_67 = lean_ctor_get(x_51, 7);
x_68 = lean_ctor_get(x_51, 8);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_69 = lean_unbox(x_29);
x_70 = l_Lean_Kernel_enableDiag(x_61, x_69);
x_71 = l_Lean_Core_instInhabitedCache___closed__2;
x_72 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_62);
lean_ctor_set(x_72, 2, x_63);
lean_ctor_set(x_72, 3, x_64);
lean_ctor_set(x_72, 4, x_65);
lean_ctor_set(x_72, 5, x_71);
lean_ctor_set(x_72, 6, x_66);
lean_ctor_set(x_72, 7, x_67);
lean_ctor_set(x_72, 8, x_68);
x_73 = lean_st_ref_set(x_7, x_72, x_52);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec_ref(x_73);
x_30 = x_12;
x_31 = x_13;
x_32 = x_15;
x_33 = x_16;
x_34 = x_17;
x_35 = x_18;
x_36 = x_19;
x_37 = x_20;
x_38 = x_21;
x_39 = x_22;
x_40 = x_23;
x_41 = x_24;
x_42 = x_7;
x_43 = x_74;
goto block_49;
}
}
block_77:
{
if (x_76 == 0)
{
goto block_75;
}
else
{
x_30 = x_12;
x_31 = x_13;
x_32 = x_15;
x_33 = x_16;
x_34 = x_17;
x_35 = x_18;
x_36 = x_19;
x_37 = x_20;
x_38 = x_21;
x_39 = x_22;
x_40 = x_23;
x_41 = x_24;
x_42 = x_7;
x_43 = x_11;
goto block_49;
}
}
}
}
static lean_object* _init_l_Lean_Core_instMonadWithOptionsCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_KVMap_instValueBool;
x_2 = l_Lean_KVMap_instValueNat;
x_3 = lean_alloc_closure((void*)(l_Lean_Core_instMonadWithOptionsCoreM___lam__0), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_64; uint8_t x_66; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_KVMap_instValueBool;
x_10 = l_Lean_KVMap_instValueNat;
x_11 = lean_st_ref_get(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 7);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 8);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 9);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 10);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 11);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
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
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 x_26 = x_2;
} else {
 lean_dec_ref(x_2);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_27);
lean_dec(x_12);
x_28 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_29 = l_Lean_Option_get___redArg(x_9, x_16, x_28);
x_66 = l_Lean_Kernel_isDiagnosticsEnabled(x_27);
lean_dec_ref(x_27);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = lean_unbox(x_29);
if (x_67 == 0)
{
x_30 = x_3;
x_31 = x_13;
goto block_37;
}
else
{
x_64 = x_66;
goto block_65;
}
}
else
{
uint8_t x_68; 
x_68 = lean_unbox(x_29);
if (x_68 == 0)
{
goto block_63;
}
else
{
x_64 = x_66;
goto block_65;
}
}
block_37:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_32 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_33 = l_Lean_Option_get___redArg(x_10, x_16, x_32);
if (lean_is_scalar(x_26)) {
 x_34 = lean_alloc_ctor(0, 13, 2);
} else {
 x_34 = x_26;
}
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_15);
lean_ctor_set(x_34, 2, x_16);
lean_ctor_set(x_34, 3, x_17);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_18);
lean_ctor_set(x_34, 6, x_19);
lean_ctor_set(x_34, 7, x_20);
lean_ctor_set(x_34, 8, x_21);
lean_ctor_set(x_34, 9, x_22);
lean_ctor_set(x_34, 10, x_23);
lean_ctor_set(x_34, 11, x_24);
lean_ctor_set(x_34, 12, x_7);
x_35 = lean_unbox(x_29);
lean_dec(x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*13, x_35);
lean_ctor_set_uint8(x_34, sizeof(void*)*13 + 1, x_25);
x_36 = lean_apply_3(x_1, x_34, x_30, x_31);
return x_36;
}
block_63:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_st_ref_take(x_3, x_13);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 5);
lean_dec(x_43);
x_44 = lean_unbox(x_29);
x_45 = l_Lean_Kernel_enableDiag(x_42, x_44);
x_46 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_39, 5, x_46);
lean_ctor_set(x_39, 0, x_45);
x_47 = lean_st_ref_set(x_3, x_39, x_40);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_30 = x_3;
x_31 = x_48;
goto block_37;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
x_51 = lean_ctor_get(x_39, 2);
x_52 = lean_ctor_get(x_39, 3);
x_53 = lean_ctor_get(x_39, 4);
x_54 = lean_ctor_get(x_39, 6);
x_55 = lean_ctor_get(x_39, 7);
x_56 = lean_ctor_get(x_39, 8);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_57 = lean_unbox(x_29);
x_58 = l_Lean_Kernel_enableDiag(x_49, x_57);
x_59 = l_Lean_Core_instInhabitedCache___closed__2;
x_60 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_50);
lean_ctor_set(x_60, 2, x_51);
lean_ctor_set(x_60, 3, x_52);
lean_ctor_set(x_60, 4, x_53);
lean_ctor_set(x_60, 5, x_59);
lean_ctor_set(x_60, 6, x_54);
lean_ctor_set(x_60, 7, x_55);
lean_ctor_set(x_60, 8, x_56);
x_61 = lean_st_ref_set(x_3, x_60, x_40);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
x_30 = x_3;
x_31 = x_62;
goto block_37;
}
}
block_65:
{
if (x_64 == 0)
{
goto block_63;
}
else
{
x_30 = x_3;
x_31 = x_13;
goto block_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_77; uint8_t x_79; 
x_6 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_KVMap_instValueBool;
x_11 = l_Lean_KVMap_instValueNat;
x_12 = lean_st_ref_get(x_4, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 7);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 8);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 9);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 10);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 11);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 x_27 = x_3;
} else {
 lean_dec_ref(x_3);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_28);
lean_dec(x_13);
x_29 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_30 = l_Lean_Option_get___redArg(x_10, x_17, x_29);
x_79 = l_Lean_Kernel_isDiagnosticsEnabled(x_28);
lean_dec_ref(x_28);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = lean_unbox(x_30);
if (x_80 == 0)
{
x_31 = x_15;
x_32 = x_16;
x_33 = x_18;
x_34 = x_19;
x_35 = x_20;
x_36 = x_21;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_8;
x_43 = x_4;
x_44 = x_14;
goto block_50;
}
else
{
x_77 = x_79;
goto block_78;
}
}
else
{
uint8_t x_81; 
x_81 = lean_unbox(x_30);
if (x_81 == 0)
{
goto block_76;
}
else
{
x_77 = x_79;
goto block_78;
}
}
block_50:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_46 = l_Lean_Option_get___redArg(x_11, x_17, x_45);
if (lean_is_scalar(x_27)) {
 x_47 = lean_alloc_ctor(0, 13, 2);
} else {
 x_47 = x_27;
}
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_32);
lean_ctor_set(x_47, 2, x_17);
lean_ctor_set(x_47, 3, x_33);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_34);
lean_ctor_set(x_47, 6, x_35);
lean_ctor_set(x_47, 7, x_36);
lean_ctor_set(x_47, 8, x_37);
lean_ctor_set(x_47, 9, x_38);
lean_ctor_set(x_47, 10, x_39);
lean_ctor_set(x_47, 11, x_40);
lean_ctor_set(x_47, 12, x_42);
x_48 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_47, sizeof(void*)*13, x_48);
lean_ctor_set_uint8(x_47, sizeof(void*)*13 + 1, x_41);
x_49 = lean_apply_3(x_2, x_47, x_43, x_44);
return x_49;
}
block_76:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_st_ref_take(x_4, x_14);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 5);
lean_dec(x_56);
x_57 = lean_unbox(x_30);
x_58 = l_Lean_Kernel_enableDiag(x_55, x_57);
x_59 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_52, 5, x_59);
lean_ctor_set(x_52, 0, x_58);
x_60 = lean_st_ref_set(x_4, x_52, x_53);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec_ref(x_60);
x_31 = x_15;
x_32 = x_16;
x_33 = x_18;
x_34 = x_19;
x_35 = x_20;
x_36 = x_21;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_8;
x_43 = x_4;
x_44 = x_61;
goto block_50;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = lean_ctor_get(x_52, 0);
x_63 = lean_ctor_get(x_52, 1);
x_64 = lean_ctor_get(x_52, 2);
x_65 = lean_ctor_get(x_52, 3);
x_66 = lean_ctor_get(x_52, 4);
x_67 = lean_ctor_get(x_52, 6);
x_68 = lean_ctor_get(x_52, 7);
x_69 = lean_ctor_get(x_52, 8);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_52);
x_70 = lean_unbox(x_30);
x_71 = l_Lean_Kernel_enableDiag(x_62, x_70);
x_72 = l_Lean_Core_instInhabitedCache___closed__2;
x_73 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_63);
lean_ctor_set(x_73, 2, x_64);
lean_ctor_set(x_73, 3, x_65);
lean_ctor_set(x_73, 4, x_66);
lean_ctor_set(x_73, 5, x_72);
lean_ctor_set(x_73, 6, x_67);
lean_ctor_set(x_73, 7, x_68);
lean_ctor_set(x_73, 8, x_69);
x_74 = lean_st_ref_set(x_4, x_73, x_53);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec_ref(x_74);
x_31 = x_15;
x_32 = x_16;
x_33 = x_18;
x_34 = x_19;
x_35 = x_20;
x_36 = x_21;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_8;
x_43 = x_4;
x_44 = x_75;
goto block_50;
}
}
block_78:
{
if (x_77 == 0)
{
goto block_76;
}
else
{
x_31 = x_15;
x_32 = x_16;
x_33 = x_18;
x_34 = x_19;
x_35 = x_20;
x_36 = x_21;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_8;
x_43 = x_4;
x_44 = x_14;
goto block_50;
}
}
}
}
static lean_object* _init_l_Lean_Core_instAddMessageContextCoreM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instAddMessageContextCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instAddMessageContextCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instAddMessageContextCoreM() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__1;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = l_Lean_Core_instAddMessageContextCoreM___closed__0;
x_12 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
lean_inc_ref(x_6);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_13, 0, x_6);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_17, 0, x_8);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_18, 0, x_7);
lean_ctor_set(x_3, 4, x_16);
lean_ctor_set(x_3, 3, x_17);
lean_ctor_set(x_3, 2, x_18);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_12);
x_19 = l_Lean_Core_instMonadEnvCoreM;
x_20 = l_Lean_Core_instAddMessageContextCoreM___closed__2;
x_21 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial), 5, 4);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_19);
lean_closure_set(x_21, 3, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_26 = l_Lean_Core_instAddMessageContextCoreM___closed__0;
x_27 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
lean_inc_ref(x_22);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_28, 0, x_22);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_31, 0, x_25);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_32, 0, x_24);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_33, 0, x_23);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_34);
x_35 = l_Lean_Core_instMonadEnvCoreM;
x_36 = l_Lean_Core_instAddMessageContextCoreM___closed__2;
x_37 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial), 5, 4);
lean_closure_set(x_37, 0, lean_box(0));
lean_closure_set(x_37, 1, x_1);
lean_closure_set(x_37, 2, x_35);
lean_closure_set(x_37, 3, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_38, 2);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_38, 3);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_38, 4);
lean_inc_ref(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
x_44 = l_Lean_Core_instAddMessageContextCoreM___closed__0;
x_45 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
lean_inc_ref(x_39);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_46, 0, x_39);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_39);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_49, 0, x_42);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_50, 0, x_41);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_51, 0, x_40);
if (lean_is_scalar(x_43)) {
 x_52 = lean_alloc_ctor(0, 5, 0);
} else {
 x_52 = x_43;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set(x_52, 4, x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_54 = l_Lean_Core_instMonadEnvCoreM;
x_55 = l_Lean_Core_instAddMessageContextCoreM___closed__2;
x_56 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial), 5, 4);
lean_closure_set(x_56, 0, lean_box(0));
lean_closure_set(x_56, 1, x_53);
lean_closure_set(x_56, 2, x_54);
lean_closure_set(x_56, 3, x_55);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc_ref(x_7);
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
lean_inc_ref(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
x_24 = lean_ctor_get(x_6, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_1);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
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
static lean_object* _init_l_Lean_Core_instMonadNameGeneratorCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed), 4, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc_ref(x_7);
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
lean_inc_ref(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 3);
lean_dec(x_9);
lean_ctor_set(x_6, 3, x_1);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
x_24 = lean_ctor_get(x_6, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_1);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
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
static lean_object* _init_l_Lean_Core_instMonadDeclNameGeneratorCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1___boxed), 4, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_21 = lean_ctor_get(x_4, 11);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_23 = lean_ctor_get(x_4, 12);
lean_inc(x_23);
lean_inc(x_21);
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
x_24 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_2);
lean_ctor_set(x_24, 4, x_13);
lean_ctor_set(x_24, 5, x_14);
lean_ctor_set(x_24, 6, x_15);
lean_ctor_set(x_24, 7, x_16);
lean_ctor_set(x_24, 8, x_17);
lean_ctor_set(x_24, 9, x_18);
lean_ctor_set(x_24, 10, x_19);
lean_ctor_set(x_24, 11, x_21);
lean_ctor_set(x_24, 12, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*13, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*13 + 1, x_22);
x_25 = lean_apply_3(x_3, x_24, x_5, x_6);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Core_instMonadRecDepthCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRecDepthCoreM___lam__0), 6, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed), 3, 0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRecDepthCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRecDepthCoreM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Core_instMonadResolveNameCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadResolveNameCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadResolveNameCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
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
lean_dec_ref(x_12);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_28 = lean_ctor_get(x_2, 11);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_30 = lean_ctor_get(x_2, 12);
lean_inc(x_30);
lean_inc(x_28);
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
x_31 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 5, x_22);
lean_ctor_set(x_31, 6, x_23);
lean_ctor_set(x_31, 7, x_24);
lean_ctor_set(x_31, 8, x_25);
lean_ctor_set(x_31, 9, x_26);
lean_ctor_set(x_31, 10, x_9);
lean_ctor_set(x_31, 11, x_28);
lean_ctor_set(x_31, 12, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*13, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*13 + 1, x_29);
x_32 = lean_apply_3(x_1, x_31, x_3, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
x_35 = lean_ctor_get(x_6, 2);
x_36 = lean_ctor_get(x_6, 3);
x_37 = lean_ctor_get(x_6, 4);
x_38 = lean_ctor_get(x_6, 5);
x_39 = lean_ctor_get(x_6, 6);
x_40 = lean_ctor_get(x_6, 7);
x_41 = lean_ctor_get(x_6, 8);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_34, x_42);
x_44 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_37);
lean_ctor_set(x_44, 5, x_38);
lean_ctor_set(x_44, 6, x_39);
lean_ctor_set(x_44, 7, x_40);
lean_ctor_set(x_44, 8, x_41);
x_45 = lean_st_ref_set(x_3, x_44, x_7);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 5);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 6);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 7);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 8);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 9);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_58 = lean_ctor_get(x_2, 11);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_60 = lean_ctor_get(x_2, 12);
lean_inc_ref(x_60);
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
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 x_61 = x_2;
} else {
 lean_dec_ref(x_2);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 13, 2);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_47);
lean_ctor_set(x_62, 1, x_48);
lean_ctor_set(x_62, 2, x_49);
lean_ctor_set(x_62, 3, x_50);
lean_ctor_set(x_62, 4, x_51);
lean_ctor_set(x_62, 5, x_52);
lean_ctor_set(x_62, 6, x_53);
lean_ctor_set(x_62, 7, x_54);
lean_ctor_set(x_62, 8, x_55);
lean_ctor_set(x_62, 9, x_56);
lean_ctor_set(x_62, 10, x_34);
lean_ctor_set(x_62, 11, x_58);
lean_ctor_set(x_62, 12, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*13, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*13 + 1, x_59);
x_63 = lean_apply_3(x_1, x_62, x_3, x_46);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withFreshMacroScope___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_Environment_mainModule(x_7);
lean_dec_ref(x_7);
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
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = l_Lean_Environment_mainModule(x_11);
lean_dec_ref(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadQuotationCoreM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_withFreshMacroScope), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadQuotationCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed), 3, 0);
x_3 = l_Lean_Core_instMonadRefCoreM;
x_4 = l_Lean_Core_instMonadQuotationCoreM___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadQuotationCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadQuotationCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_7);
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
x_10 = lean_ctor_get(x_8, 7);
lean_inc_ref(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 7);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 7, x_10);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get(x_6, 8);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_27 = lean_apply_1(x_1, x_25);
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_21);
lean_ctor_set(x_28, 4, x_22);
lean_ctor_set(x_28, 5, x_23);
lean_ctor_set(x_28, 6, x_24);
lean_ctor_set(x_28, 7, x_27);
lean_ctor_set(x_28, 8, x_26);
x_29 = lean_st_ref_set(x_3, x_28, x_7);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadInfoTreeCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed), 4, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadInfoTreeCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadInfoTreeCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_apply_1(x_1, x_8);
lean_ctor_set(x_5, 5, x_9);
x_10 = lean_st_ref_set(x_2, x_5, x_6);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 5);
x_23 = lean_ctor_get(x_5, 6);
x_24 = lean_ctor_get(x_5, 7);
x_25 = lean_ctor_get(x_5, 8);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_26 = lean_apply_1(x_1, x_22);
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_20);
lean_ctor_set(x_27, 4, x_21);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_23);
lean_ctor_set(x_27, 7, x_24);
lean_ctor_set(x_27, 8, x_25);
x_28 = lean_st_ref_set(x_2, x_27, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 5, x_10);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get(x_6, 8);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_27 = lean_apply_1(x_1, x_23);
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_21);
lean_ctor_set(x_28, 4, x_22);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_24);
lean_ctor_set(x_28, 7, x_25);
lean_ctor_set(x_28, 8, x_26);
x_29 = lean_st_ref_set(x_3, x_28, x_7);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_modifyCache___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyCache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 5);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 5);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_6, 0, x_12);
x_13 = lean_st_ref_set(x_2, x_5, x_7);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_apply_1(x_1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_5, 5, x_23);
x_24 = lean_st_ref_set(x_2, x_5, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 6);
x_35 = lean_ctor_get(x_5, 7);
x_36 = lean_ctor_get(x_5, 8);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_37 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_38);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_39 = x_6;
} else {
 lean_dec_ref(x_6);
 x_39 = lean_box(0);
}
x_40 = lean_apply_1(x_1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_30);
lean_ctor_set(x_42, 2, x_31);
lean_ctor_set(x_42, 3, x_32);
lean_ctor_set(x_42, 4, x_33);
lean_ctor_set(x_42, 5, x_41);
lean_ctor_set(x_42, 6, x_34);
lean_ctor_set(x_42, 7, x_35);
lean_ctor_set(x_42, 8, x_36);
x_43 = lean_st_ref_set(x_2, x_42, x_7);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 5);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 5);
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
lean_ctor_set(x_6, 5, x_24);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 4);
x_35 = lean_ctor_get(x_6, 6);
x_36 = lean_ctor_get(x_6, 7);
x_37 = lean_ctor_get(x_6, 8);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_38 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_39);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_40 = x_7;
} else {
 lean_dec_ref(x_7);
 x_40 = lean_box(0);
}
x_41 = lean_apply_1(x_1, x_38);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
x_43 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set(x_43, 3, x_33);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_42);
lean_ctor_set(x_43, 6, x_35);
lean_ctor_set(x_43, 7, x_36);
lean_ctor_set(x_43, 8, x_37);
x_44 = lean_st_ref_set(x_3, x_43, x_8);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_modifyInstLevelTypeCache___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyInstLevelTypeCache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 5);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 5);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_6, 1, x_12);
x_13 = lean_st_ref_set(x_2, x_5, x_7);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_apply_1(x_1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_5, 5, x_23);
x_24 = lean_st_ref_set(x_2, x_5, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 6);
x_35 = lean_ctor_get(x_5, 7);
x_36 = lean_ctor_get(x_5, 8);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_37 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_38);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_39 = x_6;
} else {
 lean_dec_ref(x_6);
 x_39 = lean_box(0);
}
x_40 = lean_apply_1(x_1, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_30);
lean_ctor_set(x_42, 2, x_31);
lean_ctor_set(x_42, 3, x_32);
lean_ctor_set(x_42, 4, x_33);
lean_ctor_set(x_42, 5, x_41);
lean_ctor_set(x_42, 6, x_34);
lean_ctor_set(x_42, 7, x_35);
lean_ctor_set(x_42, 8, x_36);
x_43 = lean_st_ref_set(x_2, x_42, x_7);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 5);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 5);
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
lean_ctor_set(x_6, 5, x_24);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 4);
x_35 = lean_ctor_get(x_6, 6);
x_36 = lean_ctor_get(x_6, 7);
x_37 = lean_ctor_get(x_6, 8);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_38 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_39);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_40 = x_7;
} else {
 lean_dec_ref(x_7);
 x_40 = lean_box(0);
}
x_41 = lean_apply_1(x_1, x_39);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set(x_43, 3, x_33);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_42);
lean_ctor_set(x_43, 6, x_35);
lean_ctor_set(x_43, 7, x_36);
lean_ctor_set(x_43, 8, x_37);
x_44 = lean_st_ref_set(x_3, x_43, x_8);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_modifyInstLevelValueCache___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyInstLevelValueCache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget(x_6, x_2);
x_13 = lean_name_eq(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget(x_19, x_2);
x_27 = lean_name_eq(x_3, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget(x_2, x_4);
x_9 = lean_array_fget(x_3, x_4);
x_10 = l_Lean_Name_hash___override(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_19 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_name_eq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_name_eq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__2;
x_52 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__0___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__2;
x_68 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_1, x_3);
x_9 = lean_name_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_name_eq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_name_eq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__8(lean_object* x_1, lean_object* x_2) {
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
return x_10;
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
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 5);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_83; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_7);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_83 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg(x_11, x_12);
if (lean_obj_tag(x_83) == 0)
{
lean_free_object(x_5);
x_13 = x_3;
x_14 = x_9;
goto block_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__8(x_2, x_85);
lean_dec(x_85);
if (x_87 == 0)
{
lean_dec(x_86);
lean_free_object(x_5);
x_13 = x_3;
x_14 = x_9;
goto block_82;
}
else
{
lean_dec(x_12);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_5, 0, x_86);
return x_5;
}
}
block_82:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_st_ref_take(x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 5);
lean_inc_ref(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_16, 5);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_2);
x_25 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
lean_inc_ref(x_25);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_2);
x_26 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_24, x_12, x_15);
lean_ctor_set(x_17, 0, x_26);
x_27 = lean_st_ref_set(x_13, x_16, x_19);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
lean_inc(x_2);
x_34 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
lean_inc_ref(x_34);
lean_ctor_set(x_15, 1, x_34);
lean_ctor_set(x_15, 0, x_2);
x_35 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_32, x_12, x_15);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_16, 5, x_36);
x_37 = lean_st_ref_set(x_13, x_16, x_19);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
x_43 = lean_ctor_get(x_16, 2);
x_44 = lean_ctor_get(x_16, 3);
x_45 = lean_ctor_get(x_16, 4);
x_46 = lean_ctor_get(x_16, 6);
x_47 = lean_ctor_get(x_16, 7);
x_48 = lean_ctor_get(x_16, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_49 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_51 = x_17;
} else {
 lean_dec_ref(x_17);
 x_51 = lean_box(0);
}
lean_inc(x_2);
x_52 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
lean_inc_ref(x_52);
lean_ctor_set(x_15, 1, x_52);
lean_ctor_set(x_15, 0, x_2);
x_53 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_49, x_12, x_15);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
x_55 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_42);
lean_ctor_set(x_55, 2, x_43);
lean_ctor_set(x_55, 3, x_44);
lean_ctor_set(x_55, 4, x_45);
lean_ctor_set(x_55, 5, x_54);
lean_ctor_set(x_55, 6, x_46);
lean_ctor_set(x_55, 7, x_47);
lean_ctor_set(x_55, 8, x_48);
x_56 = lean_st_ref_set(x_13, x_55, x_19);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_60 = lean_ctor_get(x_15, 1);
lean_inc(x_60);
lean_dec(x_15);
x_61 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_16, 6);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_16, 7);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_16, 8);
lean_inc_ref(x_68);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 lean_ctor_release(x_16, 6);
 lean_ctor_release(x_16, 7);
 lean_ctor_release(x_16, 8);
 x_69 = x_16;
} else {
 lean_dec_ref(x_16);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_71);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_72 = x_17;
} else {
 lean_dec_ref(x_17);
 x_72 = lean_box(0);
}
lean_inc(x_2);
x_73 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
lean_inc_ref(x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_70, x_12, x_74);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
if (lean_is_scalar(x_69)) {
 x_77 = lean_alloc_ctor(0, 9, 0);
} else {
 x_77 = x_69;
}
lean_ctor_set(x_77, 0, x_61);
lean_ctor_set(x_77, 1, x_62);
lean_ctor_set(x_77, 2, x_63);
lean_ctor_set(x_77, 3, x_64);
lean_ctor_set(x_77, 4, x_65);
lean_ctor_set(x_77, 5, x_76);
lean_ctor_set(x_77, 6, x_66);
lean_ctor_set(x_77, 7, x_67);
lean_ctor_set(x_77, 8, x_68);
x_78 = lean_st_ref_set(x_13, x_77, x_60);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_73);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_120; 
x_88 = lean_ctor_get(x_5, 1);
lean_inc(x_88);
lean_dec(x_5);
x_89 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_89);
lean_dec_ref(x_7);
x_90 = lean_ctor_get(x_1, 0);
lean_inc(x_90);
x_120 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg(x_89, x_90);
if (lean_obj_tag(x_120) == 0)
{
x_91 = x_3;
x_92 = x_88;
goto block_119;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__8(x_2, x_122);
lean_dec(x_122);
if (x_124 == 0)
{
lean_dec(x_123);
x_91 = x_3;
x_92 = x_88;
goto block_119;
}
else
{
lean_object* x_125; 
lean_dec(x_90);
lean_dec(x_2);
lean_dec_ref(x_1);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_88);
return x_125;
}
}
block_119:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_93 = lean_st_ref_take(x_91, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 5);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_94, 0);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 2);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_94, 3);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_94, 4);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_94, 6);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_94, 7);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_94, 8);
lean_inc_ref(x_105);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 lean_ctor_release(x_94, 3);
 lean_ctor_release(x_94, 4);
 lean_ctor_release(x_94, 5);
 lean_ctor_release(x_94, 6);
 lean_ctor_release(x_94, 7);
 lean_ctor_release(x_94, 8);
 x_106 = x_94;
} else {
 lean_dec_ref(x_94);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_95, 0);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_95, 1);
lean_inc_ref(x_108);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_109 = x_95;
} else {
 lean_dec_ref(x_95);
 x_109 = lean_box(0);
}
lean_inc(x_2);
x_110 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
lean_inc_ref(x_110);
if (lean_is_scalar(x_97)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_97;
}
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_107, x_90, x_111);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
if (lean_is_scalar(x_106)) {
 x_114 = lean_alloc_ctor(0, 9, 0);
} else {
 x_114 = x_106;
}
lean_ctor_set(x_114, 0, x_98);
lean_ctor_set(x_114, 1, x_99);
lean_ctor_set(x_114, 2, x_100);
lean_ctor_set(x_114, 3, x_101);
lean_ctor_set(x_114, 4, x_102);
lean_ctor_set(x_114, 5, x_113);
lean_ctor_set(x_114, 6, x_103);
lean_ctor_set(x_114, 7, x_104);
lean_ctor_set(x_114, 8, x_105);
x_115 = lean_st_ref_set(x_91, x_114, x_96);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5_spec__5(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateTypeLevelParams(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6;
x_2 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4;
x_4 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3;
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2;
x_6 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__9;
x_4 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__10;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__11;
x_3 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 2);
x_10 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__7;
x_11 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__12;
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
x_13 = lean_alloc_ctor(3, 2, 0);
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
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__7;
x_19 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__12;
lean_inc(x_17);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_17);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_instantiateValueLevelParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not a definition or theorem: ", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instantiateValueLevelParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instantiateValueLevelParams___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instantiateValueLevelParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_st_ref_get(x_4, x_5);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 5);
lean_inc_ref(x_96);
lean_dec(x_95);
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_94, 1);
x_99 = lean_ctor_get(x_94, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc_ref(x_100);
lean_dec_ref(x_96);
x_101 = l_Lean_ConstantInfo_name(x_1);
x_102 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg(x_100, x_101);
lean_dec(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_free_object(x_94);
x_6 = x_3;
x_7 = x_4;
x_8 = x_98;
goto block_93;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__8(x_2, x_104);
lean_dec(x_104);
if (x_106 == 0)
{
lean_dec(x_105);
lean_free_object(x_94);
x_6 = x_3;
x_7 = x_4;
x_8 = x_98;
goto block_93;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_94, 0, x_105);
return x_94;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_94, 1);
lean_inc(x_107);
lean_dec(x_94);
x_108 = lean_ctor_get(x_96, 1);
lean_inc_ref(x_108);
lean_dec_ref(x_96);
x_109 = l_Lean_ConstantInfo_name(x_1);
x_110 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Core_instantiateTypeLevelParams_spec__5___redArg(x_108, x_109);
lean_dec(x_109);
if (lean_obj_tag(x_110) == 0)
{
x_6 = x_3;
x_7 = x_4;
x_8 = x_107;
goto block_93;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__8(x_2, x_112);
lean_dec(x_112);
if (x_114 == 0)
{
lean_dec(x_113);
x_6 = x_3;
x_7 = x_4;
x_8 = x_107;
goto block_93;
}
else
{
lean_object* x_115; 
lean_dec(x_2);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_107);
return x_115;
}
}
}
block_93:
{
uint8_t x_9; uint8_t x_10; 
x_9 = 0;
x_10 = l_Lean_ConstantInfo_hasValue(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
x_11 = l_Lean_Core_instantiateValueLevelParams___closed__1;
x_12 = l_Lean_ConstantInfo_name(x_1);
x_13 = l_Lean_MessageData_ofName(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Core_instantiateValueLevelParams___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_16, x_6, x_7, x_8);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_st_ref_take(x_7, x_8);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 5);
lean_inc_ref(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_23, 5);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_2);
x_32 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_33 = l_Lean_ConstantInfo_name(x_1);
lean_inc_ref(x_32);
lean_ctor_set(x_22, 1, x_32);
lean_ctor_set(x_22, 0, x_2);
x_34 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_31, x_33, x_22);
lean_ctor_set(x_24, 1, x_34);
x_35 = lean_st_ref_set(x_7, x_23, x_26);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_32);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
lean_inc(x_2);
x_42 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_43 = l_Lean_ConstantInfo_name(x_1);
lean_inc_ref(x_42);
lean_ctor_set(x_22, 1, x_42);
lean_ctor_set(x_22, 0, x_2);
x_44 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_41, x_43, x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_23, 5, x_45);
x_46 = lean_st_ref_set(x_7, x_23, x_26);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_50 = lean_ctor_get(x_23, 0);
x_51 = lean_ctor_get(x_23, 1);
x_52 = lean_ctor_get(x_23, 2);
x_53 = lean_ctor_get(x_23, 3);
x_54 = lean_ctor_get(x_23, 4);
x_55 = lean_ctor_get(x_23, 6);
x_56 = lean_ctor_get(x_23, 7);
x_57 = lean_ctor_get(x_23, 8);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_23);
x_58 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_59);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_60 = x_24;
} else {
 lean_dec_ref(x_24);
 x_60 = lean_box(0);
}
lean_inc(x_2);
x_61 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_62 = l_Lean_ConstantInfo_name(x_1);
lean_inc_ref(x_61);
lean_ctor_set(x_22, 1, x_61);
lean_ctor_set(x_22, 0, x_2);
x_63 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_59, x_62, x_22);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_51);
lean_ctor_set(x_65, 2, x_52);
lean_ctor_set(x_65, 3, x_53);
lean_ctor_set(x_65, 4, x_54);
lean_ctor_set(x_65, 5, x_64);
lean_ctor_set(x_65, 6, x_55);
lean_ctor_set(x_65, 7, x_56);
lean_ctor_set(x_65, 8, x_57);
x_66 = lean_st_ref_set(x_7, x_65, x_26);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_70 = lean_ctor_get(x_22, 1);
lean_inc(x_70);
lean_dec(x_22);
x_71 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_23, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_23, 4);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_23, 6);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_23, 7);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_23, 8);
lean_inc_ref(x_78);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 lean_ctor_release(x_23, 5);
 lean_ctor_release(x_23, 6);
 lean_ctor_release(x_23, 7);
 lean_ctor_release(x_23, 8);
 x_79 = x_23;
} else {
 lean_dec_ref(x_23);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_81);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_82 = x_24;
} else {
 lean_dec_ref(x_24);
 x_82 = lean_box(0);
}
lean_inc(x_2);
x_83 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_84 = l_Lean_ConstantInfo_name(x_1);
lean_inc_ref(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_81, x_84, x_85);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_86);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_71);
lean_ctor_set(x_88, 1, x_72);
lean_ctor_set(x_88, 2, x_73);
lean_ctor_set(x_88, 3, x_74);
lean_ctor_set(x_88, 4, x_75);
lean_ctor_set(x_88, 5, x_87);
lean_ctor_set(x_88, 6, x_76);
lean_ctor_set(x_88, 7, x_77);
lean_ctor_set(x_88, 8, x_78);
x_89 = lean_st_ref_set(x_7, x_88, x_70);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateValueLevelParams(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_io_error_to_string(x_10);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_MessageData_ofFormat(x_13);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_ctor_get(x_2, 5);
x_19 = lean_io_error_to_string(x_16);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
lean_inc(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_2, x_5);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_io_error_to_string(x_12);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
lean_inc(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_ctor_get(x_3, 5);
x_21 = lean_io_error_to_string(x_18);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
lean_inc(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_liftIOCore___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_liftIOCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_instMonadLiftIOCoreM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLiftIOCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadLiftIOCoreM___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get(x_6, 8);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_27 = lean_apply_1(x_1, x_22);
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_21);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_23);
lean_ctor_set(x_28, 6, x_24);
lean_ctor_set(x_28, 7, x_25);
lean_ctor_set(x_28, 8, x_26);
x_29 = lean_st_ref_set(x_3, x_28, x_7);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 4);
lean_inc_ref(x_7);
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
x_10 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 12);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instMonadTraceCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadTraceCoreM___lam__0___boxed), 4, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadTraceCoreM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Core_instMonadTraceCoreM___lam__2___boxed), 3, 0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadTraceCoreM___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_saveState___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_saveState___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_saveState(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_io_get_num_heartbeats(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_4);
x_10 = lean_apply_3(x_2, x_3, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_get(x_4, x_12);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_io_get_num_heartbeats(x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_nat_sub(x_18, x_8);
lean_dec(x_8);
lean_dec(x_18);
lean_ctor_set(x_13, 1, x_19);
lean_ctor_set(x_6, 1, x_13);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_16, 0, x_6);
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
x_22 = lean_nat_sub(x_20, x_8);
lean_dec(x_8);
lean_dec(x_20);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_6, 1, x_13);
lean_ctor_set(x_6, 0, x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_io_get_num_heartbeats(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_nat_sub(x_27, x_8);
lean_dec(x_8);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_11);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_8);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
return x_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
lean_inc(x_4);
x_39 = lean_apply_3(x_2, x_3, x_4, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_st_ref_get(x_4, x_41);
lean_dec(x_4);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_io_get_num_heartbeats(x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_nat_sub(x_47, x_37);
lean_dec(x_37);
lean_dec(x_47);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_51);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_37);
lean_dec(x_4);
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_56 = x_39;
} else {
 lean_dec_ref(x_39);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_set(x_4, x_60, x_5);
lean_dec(x_4);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_IO_addHeartbeats(x_61, x_63);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_58);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_withRestoreOrSaveFull___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 6);
x_11 = lean_ctor_get(x_5, 7);
x_12 = lean_ctor_get(x_6, 7);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 6);
lean_dec(x_13);
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_ctor_set(x_6, 7, x_11);
lean_ctor_set(x_6, 6, x_10);
lean_ctor_set(x_6, 0, x_9);
x_15 = lean_st_ref_set(x_2, x_6, x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 6);
x_24 = lean_ctor_get(x_5, 7);
x_25 = lean_ctor_get(x_6, 1);
x_26 = lean_ctor_get(x_6, 2);
x_27 = lean_ctor_get(x_6, 3);
x_28 = lean_ctor_get(x_6, 4);
x_29 = lean_ctor_get(x_6, 5);
x_30 = lean_ctor_get(x_6, 8);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_22);
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_29);
lean_ctor_set(x_31, 6, x_23);
lean_ctor_set(x_31, 7, x_24);
lean_ctor_set(x_31, 8, x_30);
x_32 = lean_st_ref_set(x_2, x_31, x_7);
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
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_SavedState_restore___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_SavedState_restore___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_SavedState_restore(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_ctor_set(x_5, 1, x_10);
x_11 = lean_st_ref_set(x_2, x_5, x_6);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = l_Lean_Environment_mainModule(x_16);
lean_dec_ref(x_16);
x_18 = l_Lean_addMacroScope(x_17, x_1, x_8);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = l_Lean_Environment_mainModule(x_21);
lean_dec_ref(x_21);
x_23 = l_Lean_addMacroScope(x_22, x_1, x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
x_27 = lean_ctor_get(x_5, 2);
x_28 = lean_ctor_get(x_5, 3);
x_29 = lean_ctor_get(x_5, 4);
x_30 = lean_ctor_get(x_5, 5);
x_31 = lean_ctor_get(x_5, 6);
x_32 = lean_ctor_get(x_5, 7);
x_33 = lean_ctor_get(x_5, 8);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_26, x_34);
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_27);
lean_ctor_set(x_36, 3, x_28);
lean_ctor_set(x_36, 4, x_29);
lean_ctor_set(x_36, 5, x_30);
lean_ctor_set(x_36, 6, x_31);
lean_ctor_set(x_36, 7, x_32);
lean_ctor_set(x_36, 8, x_33);
x_37 = lean_st_ref_set(x_2, x_36, x_6);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_st_ref_get(x_2, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_43);
lean_dec(x_40);
x_44 = l_Lean_Environment_mainModule(x_43);
lean_dec_ref(x_43);
x_45 = l_Lean_addMacroScope(x_44, x_1, x_26);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_mkFreshUserName___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_mkFreshUserName(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_82; uint8_t x_84; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_KVMap_instValueBool;
x_13 = l_Lean_KVMap_instValueNat;
x_14 = lean_st_ref_get(x_6, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 6);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 7);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 8);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 9);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 10);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 11);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
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
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 x_30 = x_2;
} else {
 lean_dec_ref(x_2);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_31);
lean_dec(x_15);
x_32 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_33 = l_Lean_Option_get___redArg(x_12, x_20, x_32);
x_84 = l_Lean_Kernel_isDiagnosticsEnabled(x_31);
lean_dec_ref(x_31);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = lean_unbox(x_33);
if (x_85 == 0)
{
lean_inc(x_6);
x_34 = x_6;
x_35 = x_16;
goto block_55;
}
else
{
x_82 = x_84;
goto block_83;
}
}
else
{
uint8_t x_86; 
x_86 = lean_unbox(x_33);
if (x_86 == 0)
{
goto block_81;
}
else
{
x_82 = x_84;
goto block_83;
}
}
block_55:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_37 = l_Lean_Option_get___redArg(x_13, x_20, x_36);
if (lean_is_scalar(x_30)) {
 x_38 = lean_alloc_ctor(0, 13, 2);
} else {
 x_38 = x_30;
}
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 2, x_20);
lean_ctor_set(x_38, 3, x_21);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_22);
lean_ctor_set(x_38, 6, x_23);
lean_ctor_set(x_38, 7, x_24);
lean_ctor_set(x_38, 8, x_25);
lean_ctor_set(x_38, 9, x_26);
lean_ctor_set(x_38, 10, x_27);
lean_ctor_set(x_38, 11, x_28);
lean_ctor_set(x_38, 12, x_10);
x_39 = lean_unbox(x_33);
lean_dec(x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*13, x_39);
lean_ctor_set_uint8(x_38, sizeof(void*)*13 + 1, x_29);
x_40 = lean_apply_3(x_1, x_38, x_34, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = lean_st_ref_get(x_6, x_42);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
if (lean_is_scalar(x_17)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_17;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
if (lean_is_scalar(x_17)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_17;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_17);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_81:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_st_ref_take(x_6, x_16);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 5);
lean_dec(x_61);
x_62 = lean_unbox(x_33);
x_63 = l_Lean_Kernel_enableDiag(x_60, x_62);
x_64 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_57, 5, x_64);
lean_ctor_set(x_57, 0, x_63);
x_65 = lean_st_ref_set(x_6, x_57, x_58);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
lean_inc(x_6);
x_34 = x_6;
x_35 = x_66;
goto block_55;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_67 = lean_ctor_get(x_57, 0);
x_68 = lean_ctor_get(x_57, 1);
x_69 = lean_ctor_get(x_57, 2);
x_70 = lean_ctor_get(x_57, 3);
x_71 = lean_ctor_get(x_57, 4);
x_72 = lean_ctor_get(x_57, 6);
x_73 = lean_ctor_get(x_57, 7);
x_74 = lean_ctor_get(x_57, 8);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_57);
x_75 = lean_unbox(x_33);
x_76 = l_Lean_Kernel_enableDiag(x_67, x_75);
x_77 = l_Lean_Core_instInhabitedCache___closed__2;
x_78 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_68);
lean_ctor_set(x_78, 2, x_69);
lean_ctor_set(x_78, 3, x_70);
lean_ctor_set(x_78, 4, x_71);
lean_ctor_set(x_78, 5, x_77);
lean_ctor_set(x_78, 6, x_72);
lean_ctor_set(x_78, 7, x_73);
lean_ctor_set(x_78, 8, x_74);
x_79 = lean_st_ref_set(x_6, x_78, x_58);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
lean_inc(x_6);
x_34 = x_6;
x_35 = x_80;
goto block_55;
}
}
block_83:
{
if (x_82 == 0)
{
goto block_81;
}
else
{
lean_inc(x_6);
x_34 = x_6;
x_35 = x_16;
goto block_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_95; uint8_t x_97; 
x_6 = lean_st_mk_ref(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_KVMap_instValueBool;
x_14 = l_Lean_KVMap_instValueNat;
x_15 = lean_st_ref_get(x_7, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 7);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 8);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 9);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 10);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 11);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 x_31 = x_3;
} else {
 lean_dec_ref(x_3);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_32);
lean_dec(x_16);
x_33 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_34 = l_Lean_Option_get___redArg(x_13, x_21, x_33);
x_97 = l_Lean_Kernel_isDiagnosticsEnabled(x_32);
lean_dec_ref(x_32);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = lean_unbox(x_34);
if (x_98 == 0)
{
lean_inc(x_7);
x_35 = x_19;
x_36 = x_20;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_27;
x_43 = x_28;
x_44 = x_29;
x_45 = x_30;
x_46 = x_11;
x_47 = x_7;
x_48 = x_17;
goto block_68;
}
else
{
x_95 = x_97;
goto block_96;
}
}
else
{
uint8_t x_99; 
x_99 = lean_unbox(x_34);
if (x_99 == 0)
{
goto block_94;
}
else
{
x_95 = x_97;
goto block_96;
}
}
block_68:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_49 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_50 = l_Lean_Option_get___redArg(x_14, x_21, x_49);
if (lean_is_scalar(x_31)) {
 x_51 = lean_alloc_ctor(0, 13, 2);
} else {
 x_51 = x_31;
}
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_36);
lean_ctor_set(x_51, 2, x_21);
lean_ctor_set(x_51, 3, x_37);
lean_ctor_set(x_51, 4, x_50);
lean_ctor_set(x_51, 5, x_38);
lean_ctor_set(x_51, 6, x_39);
lean_ctor_set(x_51, 7, x_40);
lean_ctor_set(x_51, 8, x_41);
lean_ctor_set(x_51, 9, x_42);
lean_ctor_set(x_51, 10, x_43);
lean_ctor_set(x_51, 11, x_44);
lean_ctor_set(x_51, 12, x_46);
x_52 = lean_unbox(x_34);
lean_dec(x_34);
lean_ctor_set_uint8(x_51, sizeof(void*)*13, x_52);
lean_ctor_set_uint8(x_51, sizeof(void*)*13 + 1, x_45);
x_53 = lean_apply_3(x_2, x_51, x_47, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_st_ref_get(x_7, x_55);
lean_dec(x_7);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
if (lean_is_scalar(x_18)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_18;
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
if (lean_is_scalar(x_18)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_18;
}
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_18);
lean_dec(x_7);
x_64 = !lean_is_exclusive(x_53);
if (x_64 == 0)
{
return x_53;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_53, 0);
x_66 = lean_ctor_get(x_53, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
block_94:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_st_ref_take(x_7, x_17);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_70, 5);
lean_dec(x_74);
x_75 = lean_unbox(x_34);
x_76 = l_Lean_Kernel_enableDiag(x_73, x_75);
x_77 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_70, 5, x_77);
lean_ctor_set(x_70, 0, x_76);
x_78 = lean_st_ref_set(x_7, x_70, x_71);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
lean_inc(x_7);
x_35 = x_19;
x_36 = x_20;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_27;
x_43 = x_28;
x_44 = x_29;
x_45 = x_30;
x_46 = x_11;
x_47 = x_7;
x_48 = x_79;
goto block_68;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_80 = lean_ctor_get(x_70, 0);
x_81 = lean_ctor_get(x_70, 1);
x_82 = lean_ctor_get(x_70, 2);
x_83 = lean_ctor_get(x_70, 3);
x_84 = lean_ctor_get(x_70, 4);
x_85 = lean_ctor_get(x_70, 6);
x_86 = lean_ctor_get(x_70, 7);
x_87 = lean_ctor_get(x_70, 8);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_70);
x_88 = lean_unbox(x_34);
x_89 = l_Lean_Kernel_enableDiag(x_80, x_88);
x_90 = l_Lean_Core_instInhabitedCache___closed__2;
x_91 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_81);
lean_ctor_set(x_91, 2, x_82);
lean_ctor_set(x_91, 3, x_83);
lean_ctor_set(x_91, 4, x_84);
lean_ctor_set(x_91, 5, x_90);
lean_ctor_set(x_91, 6, x_85);
lean_ctor_set(x_91, 7, x_86);
lean_ctor_set(x_91, 8, x_87);
x_92 = lean_st_ref_set(x_7, x_91, x_71);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec_ref(x_92);
lean_inc(x_7);
x_35 = x_19;
x_36 = x_20;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_27;
x_43 = x_28;
x_44 = x_29;
x_45 = x_30;
x_46 = x_11;
x_47 = x_7;
x_48 = x_93;
goto block_68;
}
}
block_96:
{
if (x_95 == 0)
{
goto block_94;
}
else
{
lean_inc(x_7);
x_35 = x_19;
x_36 = x_20;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_27;
x_43 = x_28;
x_44 = x_29;
x_45 = x_30;
x_46 = x_11;
x_47 = x_7;
x_48 = x_17;
goto block_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_74; uint8_t x_76; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_KVMap_instValueBool;
x_13 = l_Lean_KVMap_instValueNat;
x_14 = lean_st_ref_get(x_6, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 7);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 8);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 9);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 10);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 11);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
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
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 x_29 = x_2;
} else {
 lean_dec_ref(x_2);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_30);
lean_dec(x_15);
x_31 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_32 = l_Lean_Option_get___redArg(x_12, x_19, x_31);
x_76 = l_Lean_Kernel_isDiagnosticsEnabled(x_30);
lean_dec_ref(x_30);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = lean_unbox(x_32);
if (x_77 == 0)
{
lean_inc(x_6);
x_33 = x_6;
x_34 = x_16;
goto block_47;
}
else
{
x_74 = x_76;
goto block_75;
}
}
else
{
uint8_t x_78; 
x_78 = lean_unbox(x_32);
if (x_78 == 0)
{
goto block_73;
}
else
{
x_74 = x_76;
goto block_75;
}
}
block_47:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_35 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_36 = l_Lean_Option_get___redArg(x_13, x_19, x_35);
if (lean_is_scalar(x_29)) {
 x_37 = lean_alloc_ctor(0, 13, 2);
} else {
 x_37 = x_29;
}
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_18);
lean_ctor_set(x_37, 2, x_19);
lean_ctor_set(x_37, 3, x_20);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_21);
lean_ctor_set(x_37, 6, x_22);
lean_ctor_set(x_37, 7, x_23);
lean_ctor_set(x_37, 8, x_24);
lean_ctor_set(x_37, 9, x_25);
lean_ctor_set(x_37, 10, x_26);
lean_ctor_set(x_37, 11, x_27);
lean_ctor_set(x_37, 12, x_10);
x_38 = lean_unbox(x_32);
lean_dec(x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*13, x_38);
lean_ctor_set_uint8(x_37, sizeof(void*)*13 + 1, x_28);
x_39 = lean_apply_3(x_1, x_37, x_33, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_st_ref_get(x_6, x_41);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_dec(x_6);
return x_39;
}
}
block_73:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_st_ref_take(x_6, x_16);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 5);
lean_dec(x_53);
x_54 = lean_unbox(x_32);
x_55 = l_Lean_Kernel_enableDiag(x_52, x_54);
x_56 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_49, 5, x_56);
lean_ctor_set(x_49, 0, x_55);
x_57 = lean_st_ref_set(x_6, x_49, x_50);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc(x_6);
x_33 = x_6;
x_34 = x_58;
goto block_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_59 = lean_ctor_get(x_49, 0);
x_60 = lean_ctor_get(x_49, 1);
x_61 = lean_ctor_get(x_49, 2);
x_62 = lean_ctor_get(x_49, 3);
x_63 = lean_ctor_get(x_49, 4);
x_64 = lean_ctor_get(x_49, 6);
x_65 = lean_ctor_get(x_49, 7);
x_66 = lean_ctor_get(x_49, 8);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_49);
x_67 = lean_unbox(x_32);
x_68 = l_Lean_Kernel_enableDiag(x_59, x_67);
x_69 = l_Lean_Core_instInhabitedCache___closed__2;
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_60);
lean_ctor_set(x_70, 2, x_61);
lean_ctor_set(x_70, 3, x_62);
lean_ctor_set(x_70, 4, x_63);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set(x_70, 6, x_64);
lean_ctor_set(x_70, 7, x_65);
lean_ctor_set(x_70, 8, x_66);
x_71 = lean_st_ref_set(x_6, x_70, x_50);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec_ref(x_71);
lean_inc(x_6);
x_33 = x_6;
x_34 = x_72;
goto block_47;
}
}
block_75:
{
if (x_74 == 0)
{
goto block_73;
}
else
{
lean_inc(x_6);
x_33 = x_6;
x_34 = x_16;
goto block_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_87; uint8_t x_89; 
x_6 = lean_st_mk_ref(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_KVMap_instValueBool;
x_14 = l_Lean_KVMap_instValueNat;
x_15 = lean_st_ref_get(x_7, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 6);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 7);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 8);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 9);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 10);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 11);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 x_30 = x_3;
} else {
 lean_dec_ref(x_3);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_31);
lean_dec(x_16);
x_32 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_33 = l_Lean_Option_get___redArg(x_13, x_20, x_32);
x_89 = l_Lean_Kernel_isDiagnosticsEnabled(x_31);
lean_dec_ref(x_31);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = lean_unbox(x_33);
if (x_90 == 0)
{
lean_inc(x_7);
x_34 = x_18;
x_35 = x_19;
x_36 = x_21;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_27;
x_43 = x_28;
x_44 = x_29;
x_45 = x_11;
x_46 = x_7;
x_47 = x_17;
goto block_60;
}
else
{
x_87 = x_89;
goto block_88;
}
}
else
{
uint8_t x_91; 
x_91 = lean_unbox(x_33);
if (x_91 == 0)
{
goto block_86;
}
else
{
x_87 = x_89;
goto block_88;
}
}
block_60:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_49 = l_Lean_Option_get___redArg(x_14, x_20, x_48);
if (lean_is_scalar(x_30)) {
 x_50 = lean_alloc_ctor(0, 13, 2);
} else {
 x_50 = x_30;
}
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_35);
lean_ctor_set(x_50, 2, x_20);
lean_ctor_set(x_50, 3, x_36);
lean_ctor_set(x_50, 4, x_49);
lean_ctor_set(x_50, 5, x_37);
lean_ctor_set(x_50, 6, x_38);
lean_ctor_set(x_50, 7, x_39);
lean_ctor_set(x_50, 8, x_40);
lean_ctor_set(x_50, 9, x_41);
lean_ctor_set(x_50, 10, x_42);
lean_ctor_set(x_50, 11, x_43);
lean_ctor_set(x_50, 12, x_45);
x_51 = lean_unbox(x_33);
lean_dec(x_33);
lean_ctor_set_uint8(x_50, sizeof(void*)*13, x_51);
lean_ctor_set_uint8(x_50, sizeof(void*)*13 + 1, x_44);
x_52 = lean_apply_3(x_2, x_50, x_46, x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_st_ref_get(x_7, x_54);
lean_dec(x_7);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_dec(x_7);
return x_52;
}
}
block_86:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_st_ref_take(x_7, x_17);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_62, 0);
x_66 = lean_ctor_get(x_62, 5);
lean_dec(x_66);
x_67 = lean_unbox(x_33);
x_68 = l_Lean_Kernel_enableDiag(x_65, x_67);
x_69 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_62, 5, x_69);
lean_ctor_set(x_62, 0, x_68);
x_70 = lean_st_ref_set(x_7, x_62, x_63);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec_ref(x_70);
lean_inc(x_7);
x_34 = x_18;
x_35 = x_19;
x_36 = x_21;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_27;
x_43 = x_28;
x_44 = x_29;
x_45 = x_11;
x_46 = x_7;
x_47 = x_71;
goto block_60;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_72 = lean_ctor_get(x_62, 0);
x_73 = lean_ctor_get(x_62, 1);
x_74 = lean_ctor_get(x_62, 2);
x_75 = lean_ctor_get(x_62, 3);
x_76 = lean_ctor_get(x_62, 4);
x_77 = lean_ctor_get(x_62, 6);
x_78 = lean_ctor_get(x_62, 7);
x_79 = lean_ctor_get(x_62, 8);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_62);
x_80 = lean_unbox(x_33);
x_81 = l_Lean_Kernel_enableDiag(x_72, x_80);
x_82 = l_Lean_Core_instInhabitedCache___closed__2;
x_83 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_73);
lean_ctor_set(x_83, 2, x_74);
lean_ctor_set(x_83, 3, x_75);
lean_ctor_set(x_83, 4, x_76);
lean_ctor_set(x_83, 5, x_82);
lean_ctor_set(x_83, 6, x_77);
lean_ctor_set(x_83, 7, x_78);
lean_ctor_set(x_83, 8, x_79);
x_84 = lean_st_ref_set(x_7, x_83, x_63);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec_ref(x_84);
lean_inc(x_7);
x_34 = x_18;
x_35 = x_19;
x_36 = x_21;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_27;
x_43 = x_28;
x_44 = x_29;
x_45 = x_11;
x_46 = x_7;
x_47 = x_85;
goto block_60;
}
}
block_88:
{
if (x_87 == 0)
{
goto block_86;
}
else
{
lean_inc(x_7);
x_34 = x_18;
x_35 = x_19;
x_36 = x_21;
x_37 = x_22;
x_38 = x_23;
x_39 = x_24;
x_40 = x_25;
x_41 = x_26;
x_42 = x_27;
x_43 = x_28;
x_44 = x_29;
x_45 = x_11;
x_46 = x_7;
x_47 = x_17;
goto block_60;
}
}
}
}
static lean_object* _init_l_Lean_Core_CoreM_toIO___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal exception #", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_105; uint8_t x_107; 
x_5 = lean_io_get_num_heartbeats(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_st_mk_ref(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_12 = lean_st_ref_get(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_KVMap_instValueBool;
x_16 = l_Lean_KVMap_instValueNat;
x_17 = lean_st_ref_get(x_9, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 6);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 7);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 9);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 10);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 11);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
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
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 x_32 = x_2;
} else {
 lean_dec_ref(x_2);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_33);
lean_dec(x_18);
x_34 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_35 = l_Lean_Option_get___redArg(x_15, x_23, x_34);
x_107 = l_Lean_Kernel_isDiagnosticsEnabled(x_33);
lean_dec_ref(x_33);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = lean_unbox(x_35);
if (x_108 == 0)
{
lean_inc(x_9);
x_36 = x_9;
x_37 = x_19;
goto block_78;
}
else
{
x_105 = x_107;
goto block_106;
}
}
else
{
uint8_t x_109; 
x_109 = lean_unbox(x_35);
if (x_109 == 0)
{
goto block_104;
}
else
{
x_105 = x_107;
goto block_106;
}
}
block_78:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_39 = l_Lean_Option_get___redArg(x_16, x_23, x_38);
if (lean_is_scalar(x_32)) {
 x_40 = lean_alloc_ctor(0, 13, 2);
} else {
 x_40 = x_32;
}
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_22);
lean_ctor_set(x_40, 2, x_23);
lean_ctor_set(x_40, 3, x_24);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_25);
lean_ctor_set(x_40, 6, x_26);
lean_ctor_set(x_40, 7, x_27);
lean_ctor_set(x_40, 8, x_6);
lean_ctor_set(x_40, 9, x_28);
lean_ctor_set(x_40, 10, x_29);
lean_ctor_set(x_40, 11, x_30);
lean_ctor_set(x_40, 12, x_13);
x_41 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*13, x_41);
lean_ctor_set_uint8(x_40, sizeof(void*)*13 + 1, x_31);
x_42 = lean_apply_3(x_1, x_40, x_36, x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_st_ref_get(x_9, x_44);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
if (lean_is_scalar(x_20)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_20;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
if (lean_is_scalar(x_20)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_20;
}
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_dec(x_20);
lean_dec(x_9);
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_dec_ref(x_42);
x_55 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_MessageData_toString(x_55, x_54);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_42);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_42, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_53, 0);
lean_inc(x_66);
lean_dec_ref(x_53);
x_67 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_68 = l_Nat_reprFast(x_66);
x_69 = lean_string_append(x_67, x_68);
lean_dec_ref(x_68);
x_70 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_42, 0, x_70);
return x_42;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_42, 1);
lean_inc(x_71);
lean_dec(x_42);
x_72 = lean_ctor_get(x_53, 0);
lean_inc(x_72);
lean_dec_ref(x_53);
x_73 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_74 = l_Nat_reprFast(x_72);
x_75 = lean_string_append(x_73, x_74);
lean_dec_ref(x_74);
x_76 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
return x_77;
}
}
}
}
block_104:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_st_ref_take(x_9, x_19);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_80, 0);
x_84 = lean_ctor_get(x_80, 5);
lean_dec(x_84);
x_85 = lean_unbox(x_35);
x_86 = l_Lean_Kernel_enableDiag(x_83, x_85);
x_87 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_80, 5, x_87);
lean_ctor_set(x_80, 0, x_86);
x_88 = lean_st_ref_set(x_9, x_80, x_81);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec_ref(x_88);
lean_inc(x_9);
x_36 = x_9;
x_37 = x_89;
goto block_78;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_90 = lean_ctor_get(x_80, 0);
x_91 = lean_ctor_get(x_80, 1);
x_92 = lean_ctor_get(x_80, 2);
x_93 = lean_ctor_get(x_80, 3);
x_94 = lean_ctor_get(x_80, 4);
x_95 = lean_ctor_get(x_80, 6);
x_96 = lean_ctor_get(x_80, 7);
x_97 = lean_ctor_get(x_80, 8);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_80);
x_98 = lean_unbox(x_35);
x_99 = l_Lean_Kernel_enableDiag(x_90, x_98);
x_100 = l_Lean_Core_instInhabitedCache___closed__2;
x_101 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_91);
lean_ctor_set(x_101, 2, x_92);
lean_ctor_set(x_101, 3, x_93);
lean_ctor_set(x_101, 4, x_94);
lean_ctor_set(x_101, 5, x_100);
lean_ctor_set(x_101, 6, x_95);
lean_ctor_set(x_101, 7, x_96);
lean_ctor_set(x_101, 8, x_97);
x_102 = lean_st_ref_set(x_9, x_101, x_81);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
lean_inc(x_9);
x_36 = x_9;
x_37 = x_103;
goto block_78;
}
}
block_106:
{
if (x_105 == 0)
{
goto block_104;
}
else
{
lean_inc(x_9);
x_36 = x_9;
x_37 = x_19;
goto block_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_118; uint8_t x_120; 
x_6 = lean_io_get_num_heartbeats(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_st_mk_ref(x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_13 = lean_st_ref_get(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_KVMap_instValueBool;
x_17 = l_Lean_KVMap_instValueNat;
x_18 = lean_st_ref_get(x_10, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_3, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 6);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 7);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 9);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 10);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 11);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 x_33 = x_3;
} else {
 lean_dec_ref(x_3);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_34);
lean_dec(x_19);
x_35 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_36 = l_Lean_Option_get___redArg(x_16, x_24, x_35);
x_120 = l_Lean_Kernel_isDiagnosticsEnabled(x_34);
lean_dec_ref(x_34);
if (x_120 == 0)
{
uint8_t x_121; 
x_121 = lean_unbox(x_36);
if (x_121 == 0)
{
lean_inc(x_10);
x_37 = x_22;
x_38 = x_23;
x_39 = x_25;
x_40 = x_26;
x_41 = x_27;
x_42 = x_28;
x_43 = x_7;
x_44 = x_29;
x_45 = x_30;
x_46 = x_31;
x_47 = x_32;
x_48 = x_14;
x_49 = x_10;
x_50 = x_20;
goto block_91;
}
else
{
x_118 = x_120;
goto block_119;
}
}
else
{
uint8_t x_122; 
x_122 = lean_unbox(x_36);
if (x_122 == 0)
{
goto block_117;
}
else
{
x_118 = x_120;
goto block_119;
}
}
block_91:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_51 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_52 = l_Lean_Option_get___redArg(x_17, x_24, x_51);
if (lean_is_scalar(x_33)) {
 x_53 = lean_alloc_ctor(0, 13, 2);
} else {
 x_53 = x_33;
}
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_24);
lean_ctor_set(x_53, 3, x_39);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_40);
lean_ctor_set(x_53, 6, x_41);
lean_ctor_set(x_53, 7, x_42);
lean_ctor_set(x_53, 8, x_43);
lean_ctor_set(x_53, 9, x_44);
lean_ctor_set(x_53, 10, x_45);
lean_ctor_set(x_53, 11, x_46);
lean_ctor_set(x_53, 12, x_48);
x_54 = lean_unbox(x_36);
lean_dec(x_36);
lean_ctor_set_uint8(x_53, sizeof(void*)*13, x_54);
lean_ctor_set_uint8(x_53, sizeof(void*)*13 + 1, x_47);
x_55 = lean_apply_3(x_2, x_53, x_49, x_50);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_st_ref_get(x_10, x_57);
lean_dec(x_10);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
if (lean_is_scalar(x_21)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_21;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
if (lean_is_scalar(x_21)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_21;
}
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_dec(x_21);
lean_dec(x_10);
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_dec_ref(x_55);
x_68 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_66);
x_69 = l_Lean_MessageData_toString(x_68, x_67);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_55);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_55, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_66, 0);
lean_inc(x_79);
lean_dec_ref(x_66);
x_80 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_81 = l_Nat_reprFast(x_79);
x_82 = lean_string_append(x_80, x_81);
lean_dec_ref(x_81);
x_83 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_55, 0, x_83);
return x_55;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_55, 1);
lean_inc(x_84);
lean_dec(x_55);
x_85 = lean_ctor_get(x_66, 0);
lean_inc(x_85);
lean_dec_ref(x_66);
x_86 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_87 = l_Nat_reprFast(x_85);
x_88 = lean_string_append(x_86, x_87);
lean_dec_ref(x_87);
x_89 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
}
}
}
block_117:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_st_ref_take(x_10, x_20);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_93, 0);
x_97 = lean_ctor_get(x_93, 5);
lean_dec(x_97);
x_98 = lean_unbox(x_36);
x_99 = l_Lean_Kernel_enableDiag(x_96, x_98);
x_100 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_93, 5, x_100);
lean_ctor_set(x_93, 0, x_99);
x_101 = lean_st_ref_set(x_10, x_93, x_94);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec_ref(x_101);
lean_inc(x_10);
x_37 = x_22;
x_38 = x_23;
x_39 = x_25;
x_40 = x_26;
x_41 = x_27;
x_42 = x_28;
x_43 = x_7;
x_44 = x_29;
x_45 = x_30;
x_46 = x_31;
x_47 = x_32;
x_48 = x_14;
x_49 = x_10;
x_50 = x_102;
goto block_91;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_103 = lean_ctor_get(x_93, 0);
x_104 = lean_ctor_get(x_93, 1);
x_105 = lean_ctor_get(x_93, 2);
x_106 = lean_ctor_get(x_93, 3);
x_107 = lean_ctor_get(x_93, 4);
x_108 = lean_ctor_get(x_93, 6);
x_109 = lean_ctor_get(x_93, 7);
x_110 = lean_ctor_get(x_93, 8);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_93);
x_111 = lean_unbox(x_36);
x_112 = l_Lean_Kernel_enableDiag(x_103, x_111);
x_113 = l_Lean_Core_instInhabitedCache___closed__2;
x_114 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_104);
lean_ctor_set(x_114, 2, x_105);
lean_ctor_set(x_114, 3, x_106);
lean_ctor_set(x_114, 4, x_107);
lean_ctor_set(x_114, 5, x_113);
lean_ctor_set(x_114, 6, x_108);
lean_ctor_set(x_114, 7, x_109);
lean_ctor_set(x_114, 8, x_110);
x_115 = lean_st_ref_set(x_10, x_114, x_94);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
lean_inc(x_10);
x_37 = x_22;
x_38 = x_23;
x_39 = x_25;
x_40 = x_26;
x_41 = x_27;
x_42 = x_28;
x_43 = x_7;
x_44 = x_29;
x_45 = x_30;
x_46 = x_31;
x_47 = x_32;
x_48 = x_14;
x_49 = x_10;
x_50 = x_116;
goto block_91;
}
}
block_119:
{
if (x_118 == 0)
{
goto block_117;
}
else
{
lean_inc(x_10);
x_37 = x_22;
x_38 = x_23;
x_39 = x_25;
x_40 = x_26;
x_41 = x_27;
x_42 = x_28;
x_43 = x_7;
x_44 = x_29;
x_45 = x_30;
x_46 = x_31;
x_47 = x_32;
x_48 = x_14;
x_49 = x_10;
x_50 = x_20;
goto block_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
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
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_19 = lean_ctor_get(x_4, 11);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_21 = lean_ctor_get(x_4, 12);
lean_inc_ref(x_21);
x_22 = lean_nat_dec_eq(x_10, x_11);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec_ref(x_2);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_4, 12);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 11);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 10);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 9);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 8);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 7);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 6);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 5);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 4);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_4, 0);
lean_dec(x_36);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_10, x_37);
lean_dec(x_10);
lean_ctor_set(x_4, 3, x_38);
x_39 = lean_apply_5(x_3, lean_box(0), x_1, x_4, x_5, x_6);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_10, x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_42, 0, x_7);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_42, 2, x_9);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_11);
lean_ctor_set(x_42, 5, x_12);
lean_ctor_set(x_42, 6, x_13);
lean_ctor_set(x_42, 7, x_14);
lean_ctor_set(x_42, 8, x_15);
lean_ctor_set(x_42, 9, x_16);
lean_ctor_set(x_42, 10, x_17);
lean_ctor_set(x_42, 11, x_19);
lean_ctor_set(x_42, 12, x_21);
lean_ctor_set_uint8(x_42, sizeof(void*)*13, x_18);
lean_ctor_set_uint8(x_42, sizeof(void*)*13 + 1, x_20);
x_43 = lean_apply_5(x_3, lean_box(0), x_1, x_42, x_5, x_6);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_44 = l_Lean_throwMaxRecDepthAt___redArg(x_2, x_12);
x_45 = lean_apply_3(x_44, x_4, x_5, x_6);
return x_45;
}
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadExceptOfEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__2;
x_2 = l_Lean_Core_withIncRecDepth___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__3;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__3;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__5;
x_2 = l_Lean_Core_withIncRecDepth___redArg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Core_instMonadCoreM___closed__1;
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 2);
x_11 = lean_ctor_get(x_6, 3);
x_12 = lean_ctor_get(x_6, 4);
x_13 = lean_ctor_get(x_6, 1);
lean_dec(x_13);
x_14 = l_Lean_Core_instAddMessageContextCoreM___closed__0;
x_15 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
lean_inc_ref(x_9);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_20, 0, x_11);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_21, 0, x_10);
lean_ctor_set(x_6, 4, x_19);
lean_ctor_set(x_6, 3, x_20);
lean_ctor_set(x_6, 2, x_21);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_18);
lean_ctor_set(x_4, 1, x_15);
x_22 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_23 = l_Lean_Core_instMonadRefCoreM;
x_24 = l_Lean_Core_instAddMessageContextCoreM;
x_25 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_24, x_4);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_2);
x_30 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__0), 6, 2);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_26);
x_31 = lean_apply_2(x_28, lean_box(0), x_30);
x_32 = lean_apply_1(x_29, lean_box(0));
x_33 = lean_apply_4(x_27, lean_box(0), lean_box(0), x_31, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_ctor_get(x_6, 2);
x_36 = lean_ctor_get(x_6, 3);
x_37 = lean_ctor_get(x_6, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
x_38 = l_Lean_Core_instAddMessageContextCoreM___closed__0;
x_39 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
lean_inc_ref(x_34);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_37);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_36);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_35);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 4, x_43);
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_46);
x_47 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_48 = l_Lean_Core_instMonadRefCoreM;
x_49 = l_Lean_Core_instAddMessageContextCoreM;
x_50 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_49, x_4);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_52);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_54);
lean_dec_ref(x_2);
x_55 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__0), 6, 2);
lean_closure_set(x_55, 0, x_3);
lean_closure_set(x_55, 1, x_51);
x_56 = lean_apply_2(x_53, lean_box(0), x_55);
x_57 = lean_apply_1(x_54, lean_box(0));
x_58 = lean_apply_4(x_52, lean_box(0), lean_box(0), x_56, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_59 = lean_ctor_get(x_4, 0);
lean_inc(x_59);
lean_dec(x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_59, 2);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_59, 3);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_59, 4);
lean_inc_ref(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Core_instAddMessageContextCoreM___closed__0;
x_66 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
lean_inc_ref(x_60);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_67, 0, x_60);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_68, 0, x_60);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_70, 0, x_63);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_71, 0, x_62);
x_72 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_72, 0, x_61);
if (lean_is_scalar(x_64)) {
 x_73 = lean_alloc_ctor(0, 5, 0);
} else {
 x_73 = x_64;
}
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_65);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_71);
lean_ctor_set(x_73, 4, x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
x_75 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_76 = l_Lean_Core_instMonadRefCoreM;
x_77 = l_Lean_Core_instAddMessageContextCoreM;
x_78 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_77, x_74);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_78);
x_80 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_80);
lean_dec_ref(x_1);
x_81 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_82);
lean_dec_ref(x_2);
x_83 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__0), 6, 2);
lean_closure_set(x_83, 0, x_3);
lean_closure_set(x_83, 1, x_79);
x_84 = lean_apply_2(x_81, lean_box(0), x_83);
x_85 = lean_apply_1(x_82, lean_box(0));
x_86 = lean_apply_4(x_80, lean_box(0), lean_box(0), x_84, x_85);
return x_86;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withIncRecDepth___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Core_instMonadCoreM___closed__1;
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 2);
x_11 = lean_ctor_get(x_6, 3);
x_12 = lean_ctor_get(x_6, 4);
x_13 = lean_ctor_get(x_6, 1);
lean_dec(x_13);
x_14 = l_Lean_Core_instAddMessageContextCoreM___closed__0;
x_15 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
lean_inc_ref(x_9);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_20, 0, x_11);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_21, 0, x_10);
lean_ctor_set(x_6, 4, x_19);
lean_ctor_set(x_6, 3, x_20);
lean_ctor_set(x_6, 2, x_21);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_18);
lean_ctor_set(x_4, 1, x_15);
x_22 = lean_ctor_get(x_1, 11);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_st_ref_get(x_25, x_3);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec_ref(x_26);
x_36 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_37 = l_Lean_Core_instMonadRefCoreM;
x_38 = l_Lean_Core_instAddMessageContextCoreM;
x_39 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_38, x_4);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_39);
x_41 = l_Lean_throwInterruptException___redArg(x_40);
x_42 = lean_apply_3(x_41, x_1, x_2, x_35);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_ctor_get(x_6, 2);
x_45 = lean_ctor_get(x_6, 3);
x_46 = lean_ctor_get(x_6, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_6);
x_47 = l_Lean_Core_instAddMessageContextCoreM___closed__0;
x_48 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
lean_inc_ref(x_43);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_49, 0, x_43);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_50, 0, x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_52, 0, x_46);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_53, 0, x_45);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_54, 0, x_44);
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_55, 3, x_53);
lean_ctor_set(x_55, 4, x_52);
lean_ctor_set(x_4, 1, x_48);
lean_ctor_set(x_4, 0, x_55);
x_56 = lean_ctor_get(x_1, 11);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec_ref(x_56);
x_60 = lean_st_ref_get(x_59, x_3);
lean_dec(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_64 = x_60;
} else {
 lean_dec_ref(x_60);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec_ref(x_60);
x_68 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_69 = l_Lean_Core_instMonadRefCoreM;
x_70 = l_Lean_Core_instAddMessageContextCoreM;
x_71 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_70, x_4);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_71);
x_73 = l_Lean_throwInterruptException___redArg(x_72);
x_74 = lean_apply_3(x_73, x_1, x_2, x_67);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_75 = lean_ctor_get(x_4, 0);
lean_inc(x_75);
lean_dec(x_4);
x_76 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_75, 2);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_75, 3);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_75, 4);
lean_inc_ref(x_79);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 x_80 = x_75;
} else {
 lean_dec_ref(x_75);
 x_80 = lean_box(0);
}
x_81 = l_Lean_Core_instAddMessageContextCoreM___closed__0;
x_82 = l_Lean_Core_instAddMessageContextCoreM___closed__1;
lean_inc_ref(x_76);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_83, 0, x_76);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_84, 0, x_76);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_86, 0, x_79);
x_87 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_87, 0, x_78);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_88, 0, x_77);
if (lean_is_scalar(x_80)) {
 x_89 = lean_alloc_ctor(0, 5, 0);
} else {
 x_89 = x_80;
}
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_81);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_87);
lean_ctor_set(x_89, 4, x_86);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_82);
x_91 = lean_ctor_get(x_1, 11);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_90);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_3);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec_ref(x_91);
x_95 = lean_st_ref_get(x_94, x_3);
lean_dec(x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_90);
lean_dec(x_2);
lean_dec_ref(x_1);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_99 = x_95;
} else {
 lean_dec_ref(x_95);
 x_99 = lean_box(0);
}
x_100 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_dec_ref(x_95);
x_103 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_104 = l_Lean_Core_instMonadRefCoreM;
x_105 = l_Lean_Core_instAddMessageContextCoreM;
x_106 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_105, x_90);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_104);
lean_ctor_set(x_107, 2, x_106);
x_108 = l_Lean_throwInterruptException___redArg(x_107);
x_109 = lean_apply_3(x_108, x_1, x_2, x_102);
return x_109;
}
}
}
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3762_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3762_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moduleNameAtTimeout", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3762_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3762_;
x_2 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3762_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3762_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("include module name in deterministic timeout error messages.\nRemark: we set this option to false to increase the stability of our test suite", 140, 140);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3762_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3762_;
x_2 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3762_;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3762_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3762_;
x_2 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3762_;
x_3 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_927_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3762_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3762_;
x_3 = l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3762_;
x_4 = l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3762_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_81_;
x_2 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(deterministic) timeout", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", maximum number of heartbeats (", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") has been reached", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Use `set_option ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" <num>` to set the limit.", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_debug_moduleNameAtTimeout;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" at `", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_39; uint8_t x_40; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 5);
x_39 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__12;
x_40 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_6, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_8 = x_41;
goto block_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__13;
x_43 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_40);
x_44 = lean_string_append(x_42, x_43);
lean_dec_ref(x_43);
x_45 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__14;
x_46 = lean_string_append(x_44, x_45);
x_8 = x_46;
goto block_38;
}
block_38:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_9 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__1;
x_10 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__3;
x_11 = l_Lean_stringToMessageData(x_8);
lean_dec_ref(x_8);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__5;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(1000u);
x_16 = lean_nat_div(x_3, x_15);
x_17 = l_Nat_reprFast(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__7;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__9;
x_24 = l_Lean_MessageData_ofName(x_2);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__11;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_note(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Core_instantiateValueLevelParams___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_useDiagnosticMsg;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_throwMaxHeartbeat___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_throwMaxHeartbeat___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_throwMaxHeartbeat(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_io_get_num_heartbeats(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_4, 8);
x_13 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_8);
x_16 = lean_box(0);
x_17 = l_Lean_Name_str___override(x_16, x_1);
x_18 = l_Lean_Core_throwMaxHeartbeat___redArg(x_17, x_2, x_3, x_4, x_11);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_ctor_get(x_4, 8);
x_22 = lean_nat_sub(x_19, x_21);
lean_dec(x_19);
x_23 = lean_nat_dec_lt(x_3, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_box(0);
x_27 = l_Lean_Name_str___override(x_26, x_1);
x_28 = l_Lean_Core_throwMaxHeartbeat___redArg(x_27, x_2, x_3, x_4, x_20);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_checkMaxHeartbeatsCore(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 9);
x_5 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_81_;
x_6 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_1, x_5, x_4, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkMaxHeartbeats(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_interruptExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 11);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_st_ref_get(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkSystem(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_io_get_num_heartbeats(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_22 = lean_ctor_get(x_2, 11);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_24 = lean_ctor_get(x_2, 12);
lean_inc(x_24);
lean_inc(x_22);
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
x_25 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_14);
lean_ctor_set(x_25, 4, x_15);
lean_ctor_set(x_25, 5, x_16);
lean_ctor_set(x_25, 6, x_17);
lean_ctor_set(x_25, 7, x_18);
lean_ctor_set(x_25, 8, x_6);
lean_ctor_set(x_25, 9, x_19);
lean_ctor_set(x_25, 10, x_20);
lean_ctor_set(x_25, 11, x_22);
lean_ctor_set(x_25, 12, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*13, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*13 + 1, x_23);
x_26 = lean_apply_3(x_1, x_25, x_3, x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_2(x_2, lean_box(0), x_1);
x_7 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___redArg___lam__0), 5, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
x_9 = lean_apply_1(x_6, lean_box(0));
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 6);
lean_dec(x_8);
lean_ctor_set(x_5, 6, x_1);
x_9 = lean_st_ref_set(x_2, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
x_19 = lean_ctor_get(x_5, 3);
x_20 = lean_ctor_get(x_5, 4);
x_21 = lean_ctor_get(x_5, 5);
x_22 = lean_ctor_get(x_5, 7);
x_23 = lean_ctor_get(x_5, 8);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_20);
lean_ctor_set(x_24, 5, x_21);
lean_ctor_set(x_24, 6, x_1);
lean_ctor_set(x_24, 7, x_22);
lean_ctor_set(x_24, 8, x_23);
x_25 = lean_st_ref_set(x_2, x_24, x_6);
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
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_setMessageLog___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_setMessageLog___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_setMessageLog(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_resetMessageLog___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_resetMessageLog___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_resetMessageLog___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_resetMessageLog___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Core_resetMessageLog___redArg___closed__0;
x_4 = l_Lean_Core_resetMessageLog___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_resetMessageLog___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Core_resetMessageLog___redArg___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Core_resetMessageLog___redArg___closed__3;
x_4 = l_Lean_Core_setMessageLog___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_resetMessageLog___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_resetMessageLog___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_resetMessageLog(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 6);
lean_inc_ref(x_6);
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
x_9 = lean_ctor_get(x_7, 6);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getMessageLog___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getMessageLog___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getMessageLog(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 6);
lean_inc_ref(x_7);
x_8 = l_Lean_MessageLog_markAllReported(x_7);
lean_ctor_set(x_4, 6, x_8);
x_9 = lean_st_ref_set(x_1, x_4, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_17 = lean_ctor_get(x_4, 3);
x_18 = lean_ctor_get(x_4, 4);
x_19 = lean_ctor_get(x_4, 5);
x_20 = lean_ctor_get(x_4, 6);
x_21 = lean_ctor_get(x_4, 7);
x_22 = lean_ctor_get(x_4, 8);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
lean_inc_ref(x_20);
x_23 = l_Lean_MessageLog_markAllReported(x_20);
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_17);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_19);
lean_ctor_set(x_24, 6, x_23);
lean_ctor_set(x_24, 7, x_21);
lean_ctor_set(x_24, 8, x_22);
x_25 = lean_st_ref_set(x_1, x_24, x_5);
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
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptyMessageLog___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getAndEmptyMessageLog___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptyMessageLog(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 8);
x_8 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
lean_ctor_set(x_4, 8, x_8);
x_9 = lean_st_ref_set(x_1, x_4, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_17 = lean_ctor_get(x_4, 3);
x_18 = lean_ctor_get(x_4, 4);
x_19 = lean_ctor_get(x_4, 5);
x_20 = lean_ctor_get(x_4, 6);
x_21 = lean_ctor_get(x_4, 7);
x_22 = lean_ctor_get(x_4, 8);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_23 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_17);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_19);
lean_ctor_set(x_24, 6, x_20);
lean_ctor_set(x_24, 7, x_21);
lean_ctor_set(x_24, 8, x_23);
x_25 = lean_st_ref_set(x_1, x_24, x_5);
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
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptySnapshotTasks___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getAndEmptySnapshotTasks___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptySnapshotTasks(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 6);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_MessageLog_hasErrors(x_7);
lean_dec_ref(x_7);
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
x_12 = lean_ctor_get(x_10, 6);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = l_Lean_MessageLog_hasErrors(x_12);
lean_dec_ref(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___lam__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___lam__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___lam__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Core_instMonadLogCoreM___lam__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
return x_6;
}
else
{
return x_1;
}
}
case 1:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_3, 1);
x_10 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_;
x_11 = lean_string_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
x_13 = lean_string_dec_eq(x_9, x_12);
if (x_13 == 0)
{
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__2;
x_15 = lean_string_dec_eq(x_8, x_14);
if (x_15 == 0)
{
return x_15;
}
else
{
return x_1;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__3;
x_17 = lean_string_dec_eq(x_8, x_16);
if (x_17 == 0)
{
return x_17;
}
else
{
return x_1;
}
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
default: 
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_113; 
x_113 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
if (x_113 == 0)
{
x_5 = x_2;
x_6 = x_3;
x_7 = x_4;
goto block_112;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_1, 4);
lean_inc(x_114);
x_115 = lean_box(x_113);
x_116 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__3___boxed), 2, 1);
lean_closure_set(x_116, 0, x_115);
x_117 = l_Lean_MessageData_hasTag(x_116, x_114);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_1);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_4);
return x_119;
}
else
{
x_5 = x_2;
x_6 = x_3;
x_7 = x_4;
goto block_112;
}
}
block_112:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_5, 6);
x_16 = lean_ctor_get(x_5, 7);
x_17 = lean_ctor_get(x_11, 6);
lean_inc(x_16);
lean_inc(x_15);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_15);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_1, 4, x_18);
x_19 = l_Lean_MessageLog_add(x_1, x_17);
lean_ctor_set(x_11, 6, x_19);
x_20 = lean_st_ref_set(x_6, x_11, x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_27 = lean_ctor_get(x_8, 1);
x_28 = lean_ctor_get(x_1, 4);
x_29 = lean_ctor_get(x_5, 6);
x_30 = lean_ctor_get(x_5, 7);
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
x_33 = lean_ctor_get(x_11, 2);
x_34 = lean_ctor_get(x_11, 3);
x_35 = lean_ctor_get(x_11, 4);
x_36 = lean_ctor_get(x_11, 5);
x_37 = lean_ctor_get(x_11, 6);
x_38 = lean_ctor_get(x_11, 7);
x_39 = lean_ctor_get(x_11, 8);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
lean_inc(x_30);
lean_inc(x_29);
lean_ctor_set(x_8, 1, x_30);
lean_ctor_set(x_8, 0, x_29);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_28);
lean_ctor_set(x_1, 4, x_40);
x_41 = l_Lean_MessageLog_add(x_1, x_37);
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_33);
lean_ctor_set(x_42, 3, x_34);
lean_ctor_set(x_42, 4, x_35);
lean_ctor_set(x_42, 5, x_36);
lean_ctor_set(x_42, 6, x_41);
lean_ctor_set(x_42, 7, x_38);
lean_ctor_set(x_42, 8, x_39);
x_43 = lean_st_ref_set(x_6, x_42, x_27);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get(x_8, 1);
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
x_52 = lean_ctor_get(x_1, 2);
x_53 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_54 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_55 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_56 = lean_ctor_get(x_1, 3);
x_57 = lean_ctor_get(x_1, 4);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
x_58 = lean_ctor_get(x_5, 6);
x_59 = lean_ctor_get(x_5, 7);
x_60 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_48, 4);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_48, 5);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_48, 6);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_48, 7);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_48, 8);
lean_inc_ref(x_68);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 lean_ctor_release(x_48, 5);
 lean_ctor_release(x_48, 6);
 lean_ctor_release(x_48, 7);
 lean_ctor_release(x_48, 8);
 x_69 = x_48;
} else {
 lean_dec_ref(x_48);
 x_69 = lean_box(0);
}
lean_inc(x_59);
lean_inc(x_58);
lean_ctor_set(x_8, 1, x_59);
lean_ctor_set(x_8, 0, x_58);
x_70 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_70, 0, x_8);
lean_ctor_set(x_70, 1, x_57);
x_71 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_71, 0, x_50);
lean_ctor_set(x_71, 1, x_51);
lean_ctor_set(x_71, 2, x_52);
lean_ctor_set(x_71, 3, x_56);
lean_ctor_set(x_71, 4, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*5, x_53);
lean_ctor_set_uint8(x_71, sizeof(void*)*5 + 1, x_54);
lean_ctor_set_uint8(x_71, sizeof(void*)*5 + 2, x_55);
x_72 = l_Lean_MessageLog_add(x_71, x_66);
if (lean_is_scalar(x_69)) {
 x_73 = lean_alloc_ctor(0, 9, 0);
} else {
 x_73 = x_69;
}
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_61);
lean_ctor_set(x_73, 2, x_62);
lean_ctor_set(x_73, 3, x_63);
lean_ctor_set(x_73, 4, x_64);
lean_ctor_set(x_73, 5, x_65);
lean_ctor_set(x_73, 6, x_72);
lean_ctor_set(x_73, 7, x_67);
lean_ctor_set(x_73, 8, x_68);
x_74 = lean_st_ref_set(x_6, x_73, x_49);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_79 = lean_ctor_get(x_8, 0);
x_80 = lean_ctor_get(x_8, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_8);
x_81 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_1, 2);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_85 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_86 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_87 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_1, 4);
lean_inc(x_88);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 x_89 = x_1;
} else {
 lean_dec_ref(x_1);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_5, 6);
x_91 = lean_ctor_get(x_5, 7);
x_92 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_79, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_79, 3);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_79, 4);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_79, 5);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_79, 6);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_79, 7);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_79, 8);
lean_inc_ref(x_100);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 lean_ctor_release(x_79, 4);
 lean_ctor_release(x_79, 5);
 lean_ctor_release(x_79, 6);
 lean_ctor_release(x_79, 7);
 lean_ctor_release(x_79, 8);
 x_101 = x_79;
} else {
 lean_dec_ref(x_79);
 x_101 = lean_box(0);
}
lean_inc(x_91);
lean_inc(x_90);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_90);
lean_ctor_set(x_102, 1, x_91);
x_103 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_88);
if (lean_is_scalar(x_89)) {
 x_104 = lean_alloc_ctor(0, 5, 3);
} else {
 x_104 = x_89;
}
lean_ctor_set(x_104, 0, x_81);
lean_ctor_set(x_104, 1, x_82);
lean_ctor_set(x_104, 2, x_83);
lean_ctor_set(x_104, 3, x_87);
lean_ctor_set(x_104, 4, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*5, x_84);
lean_ctor_set_uint8(x_104, sizeof(void*)*5 + 1, x_85);
lean_ctor_set_uint8(x_104, sizeof(void*)*5 + 2, x_86);
x_105 = l_Lean_MessageLog_add(x_104, x_98);
if (lean_is_scalar(x_101)) {
 x_106 = lean_alloc_ctor(0, 9, 0);
} else {
 x_106 = x_101;
}
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_94);
lean_ctor_set(x_106, 3, x_95);
lean_ctor_set(x_106, 4, x_96);
lean_ctor_set(x_106, 5, x_97);
lean_ctor_set(x_106, 6, x_105);
lean_ctor_set(x_106, 7, x_99);
lean_ctor_set(x_106, 8, x_100);
x_107 = lean_st_ref_set(x_6, x_106, x_80);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRefCoreM___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__0___boxed), 3, 0);
x_2 = l_Lean_Core_instMonadLogCoreM___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__2___boxed), 3, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__1___boxed), 3, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__4___boxed), 4, 0);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Core_instMonadLogCoreM___lam__3(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadLogCoreM___lam__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 8);
x_9 = lean_array_push(x_8, x_1);
lean_ctor_set(x_5, 8, x_9);
x_10 = lean_st_ref_set(x_2, x_5, x_6);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 5);
x_23 = lean_ctor_get(x_5, 6);
x_24 = lean_ctor_get(x_5, 7);
x_25 = lean_ctor_get(x_5, 8);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_26 = lean_array_push(x_25, x_1);
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_20);
lean_ctor_set(x_27, 4, x_21);
lean_ctor_set(x_27, 5, x_22);
lean_ctor_set(x_27, 6, x_23);
lean_ctor_set(x_27, 7, x_24);
lean_ctor_set(x_27, 8, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_logSnapshotTask___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_logSnapshotTask___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_logSnapshotTask(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_IO_addHeartbeats(x_1, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_4(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_46; uint8_t x_71; 
x_18 = lean_st_mk_ref(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_22 = lean_st_ref_get(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_st_ref_get(x_19, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_3);
lean_closure_set(x_29, 2, x_16);
x_30 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_31 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_4, x_30);
x_71 = l_Lean_Kernel_isDiagnosticsEnabled(x_28);
lean_dec_ref(x_28);
if (x_71 == 0)
{
if (x_31 == 0)
{
lean_inc(x_19);
x_32 = x_19;
x_33 = x_27;
goto block_45;
}
else
{
x_46 = x_71;
goto block_70;
}
}
else
{
x_46 = x_31;
goto block_70;
}
block_45:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_35 = l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(x_4, x_34);
x_36 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_6);
lean_ctor_set(x_36, 2, x_4);
lean_ctor_set(x_36, 3, x_7);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_8);
lean_ctor_set(x_36, 6, x_9);
lean_ctor_set(x_36, 7, x_10);
lean_ctor_set(x_36, 8, x_11);
lean_ctor_set(x_36, 9, x_12);
lean_ctor_set(x_36, 10, x_13);
lean_ctor_set(x_36, 11, x_14);
lean_ctor_set(x_36, 12, x_23);
lean_ctor_set_uint8(x_36, sizeof(void*)*13, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*13 + 1, x_15);
x_37 = l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(x_29, x_36, x_32, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = lean_st_ref_get(x_19, x_39);
lean_dec(x_19);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_dec(x_19);
return x_37;
}
}
block_70:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_st_ref_take(x_19, x_27);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 5);
lean_dec(x_52);
x_53 = l_Lean_Kernel_enableDiag(x_51, x_31);
x_54 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_48, 5, x_54);
lean_ctor_set(x_48, 0, x_53);
x_55 = lean_st_ref_set(x_19, x_48, x_49);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_19);
x_32 = x_19;
x_33 = x_56;
goto block_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
x_59 = lean_ctor_get(x_48, 2);
x_60 = lean_ctor_get(x_48, 3);
x_61 = lean_ctor_get(x_48, 4);
x_62 = lean_ctor_get(x_48, 6);
x_63 = lean_ctor_get(x_48, 7);
x_64 = lean_ctor_get(x_48, 8);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_65 = l_Lean_Kernel_enableDiag(x_57, x_31);
x_66 = l_Lean_Core_instInhabitedCache___closed__2;
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_58);
lean_ctor_set(x_67, 2, x_59);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_61);
lean_ctor_set(x_67, 5, x_66);
lean_ctor_set(x_67, 6, x_62);
lean_ctor_set(x_67, 7, x_63);
lean_ctor_set(x_67, 8, x_64);
x_68 = lean_st_ref_set(x_19, x_67, x_49);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
lean_inc(x_19);
x_32 = x_19;
x_33 = x_69;
goto block_45;
}
}
else
{
lean_inc(x_19);
x_32 = x_19;
x_33 = x_27;
goto block_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_DeclNameGenerator_mkChild(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_4, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_14, 3);
lean_dec(x_17);
lean_ctor_set(x_14, 3, x_12);
x_18 = lean_st_ref_set(x_4, x_14, x_15);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_st_ref_get(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_io_get_num_heartbeats(x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_21, 3);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 7);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 8);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 9);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 10);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
lean_dec_ref(x_3);
lean_ctor_set(x_21, 3, x_11);
x_39 = lean_nat_sub(x_26, x_35);
lean_dec(x_26);
x_40 = lean_box(x_38);
x_41 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 17, 15);
lean_closure_set(x_41, 0, x_21);
lean_closure_set(x_41, 1, x_39);
lean_closure_set(x_41, 2, x_1);
lean_closure_set(x_41, 3, x_30);
lean_closure_set(x_41, 4, x_28);
lean_closure_set(x_41, 5, x_29);
lean_closure_set(x_41, 6, x_31);
lean_closure_set(x_41, 7, x_32);
lean_closure_set(x_41, 8, x_33);
lean_closure_set(x_41, 9, x_34);
lean_closure_set(x_41, 10, x_35);
lean_closure_set(x_41, 11, x_36);
lean_closure_set(x_41, 12, x_37);
lean_closure_set(x_41, 13, x_2);
lean_closure_set(x_41, 14, x_40);
lean_ctor_set(x_23, 0, x_41);
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_42 = lean_ctor_get(x_23, 0);
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
x_45 = lean_ctor_get(x_21, 2);
x_46 = lean_ctor_get(x_21, 4);
x_47 = lean_ctor_get(x_21, 5);
x_48 = lean_ctor_get(x_21, 6);
x_49 = lean_ctor_get(x_21, 7);
x_50 = lean_ctor_get(x_21, 8);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_51 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 5);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 6);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 7);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 8);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 9);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 10);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
lean_dec_ref(x_3);
x_62 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_62, 0, x_43);
lean_ctor_set(x_62, 1, x_44);
lean_ctor_set(x_62, 2, x_45);
lean_ctor_set(x_62, 3, x_11);
lean_ctor_set(x_62, 4, x_46);
lean_ctor_set(x_62, 5, x_47);
lean_ctor_set(x_62, 6, x_48);
lean_ctor_set(x_62, 7, x_49);
lean_ctor_set(x_62, 8, x_50);
x_63 = lean_nat_sub(x_42, x_58);
lean_dec(x_42);
x_64 = lean_box(x_61);
x_65 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 17, 15);
lean_closure_set(x_65, 0, x_62);
lean_closure_set(x_65, 1, x_63);
lean_closure_set(x_65, 2, x_1);
lean_closure_set(x_65, 3, x_53);
lean_closure_set(x_65, 4, x_51);
lean_closure_set(x_65, 5, x_52);
lean_closure_set(x_65, 6, x_54);
lean_closure_set(x_65, 7, x_55);
lean_closure_set(x_65, 8, x_56);
lean_closure_set(x_65, 9, x_57);
lean_closure_set(x_65, 10, x_58);
lean_closure_set(x_65, 11, x_59);
lean_closure_set(x_65, 12, x_60);
lean_closure_set(x_65, 13, x_2);
lean_closure_set(x_65, 14, x_64);
lean_ctor_set(x_23, 0, x_65);
return x_23;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_66 = lean_ctor_get(x_23, 0);
x_67 = lean_ctor_get(x_23, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_23);
x_68 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_21, 4);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_21, 5);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_21, 6);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_21, 7);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_21, 8);
lean_inc_ref(x_75);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 lean_ctor_release(x_21, 6);
 lean_ctor_release(x_21, 7);
 lean_ctor_release(x_21, 8);
 x_76 = x_21;
} else {
 lean_dec_ref(x_21);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_3, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_3, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_3, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_3, 7);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 8);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 9);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 10);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
lean_dec_ref(x_3);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_68);
lean_ctor_set(x_88, 1, x_69);
lean_ctor_set(x_88, 2, x_70);
lean_ctor_set(x_88, 3, x_11);
lean_ctor_set(x_88, 4, x_71);
lean_ctor_set(x_88, 5, x_72);
lean_ctor_set(x_88, 6, x_73);
lean_ctor_set(x_88, 7, x_74);
lean_ctor_set(x_88, 8, x_75);
x_89 = lean_nat_sub(x_66, x_84);
lean_dec(x_66);
x_90 = lean_box(x_87);
x_91 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 17, 15);
lean_closure_set(x_91, 0, x_88);
lean_closure_set(x_91, 1, x_89);
lean_closure_set(x_91, 2, x_1);
lean_closure_set(x_91, 3, x_79);
lean_closure_set(x_91, 4, x_77);
lean_closure_set(x_91, 5, x_78);
lean_closure_set(x_91, 6, x_80);
lean_closure_set(x_91, 7, x_81);
lean_closure_set(x_91, 8, x_82);
lean_closure_set(x_91, 9, x_83);
lean_closure_set(x_91, 10, x_84);
lean_closure_set(x_91, 11, x_85);
lean_closure_set(x_91, 12, x_86);
lean_closure_set(x_91, 13, x_2);
lean_closure_set(x_91, 14, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_67);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_93 = lean_ctor_get(x_14, 0);
x_94 = lean_ctor_get(x_14, 1);
x_95 = lean_ctor_get(x_14, 2);
x_96 = lean_ctor_get(x_14, 4);
x_97 = lean_ctor_get(x_14, 5);
x_98 = lean_ctor_get(x_14, 6);
x_99 = lean_ctor_get(x_14, 7);
x_100 = lean_ctor_get(x_14, 8);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_14);
x_101 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_101, 0, x_93);
lean_ctor_set(x_101, 1, x_94);
lean_ctor_set(x_101, 2, x_95);
lean_ctor_set(x_101, 3, x_12);
lean_ctor_set(x_101, 4, x_96);
lean_ctor_set(x_101, 5, x_97);
lean_ctor_set(x_101, 6, x_98);
lean_ctor_set(x_101, 7, x_99);
lean_ctor_set(x_101, 8, x_100);
x_102 = lean_st_ref_set(x_4, x_101, x_15);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = lean_st_ref_get(x_4, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec_ref(x_104);
x_107 = lean_io_get_num_heartbeats(x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 2);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_105, 4);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_105, 5);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_105, 6);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_105, 7);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_105, 8);
lean_inc_ref(x_118);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 lean_ctor_release(x_105, 2);
 lean_ctor_release(x_105, 3);
 lean_ctor_release(x_105, 4);
 lean_ctor_release(x_105, 5);
 lean_ctor_release(x_105, 6);
 lean_ctor_release(x_105, 7);
 lean_ctor_release(x_105, 8);
 x_119 = x_105;
} else {
 lean_dec_ref(x_105);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_3, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_3, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_3, 5);
lean_inc(x_124);
x_125 = lean_ctor_get(x_3, 6);
lean_inc(x_125);
x_126 = lean_ctor_get(x_3, 7);
lean_inc(x_126);
x_127 = lean_ctor_get(x_3, 8);
lean_inc(x_127);
x_128 = lean_ctor_get(x_3, 9);
lean_inc(x_128);
x_129 = lean_ctor_get(x_3, 10);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
lean_dec_ref(x_3);
if (lean_is_scalar(x_119)) {
 x_131 = lean_alloc_ctor(0, 9, 0);
} else {
 x_131 = x_119;
}
lean_ctor_set(x_131, 0, x_111);
lean_ctor_set(x_131, 1, x_112);
lean_ctor_set(x_131, 2, x_113);
lean_ctor_set(x_131, 3, x_11);
lean_ctor_set(x_131, 4, x_114);
lean_ctor_set(x_131, 5, x_115);
lean_ctor_set(x_131, 6, x_116);
lean_ctor_set(x_131, 7, x_117);
lean_ctor_set(x_131, 8, x_118);
x_132 = lean_nat_sub(x_108, x_127);
lean_dec(x_108);
x_133 = lean_box(x_130);
x_134 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 17, 15);
lean_closure_set(x_134, 0, x_131);
lean_closure_set(x_134, 1, x_132);
lean_closure_set(x_134, 2, x_1);
lean_closure_set(x_134, 3, x_122);
lean_closure_set(x_134, 4, x_120);
lean_closure_set(x_134, 5, x_121);
lean_closure_set(x_134, 6, x_123);
lean_closure_set(x_134, 7, x_124);
lean_closure_set(x_134, 8, x_125);
lean_closure_set(x_134, 9, x_126);
lean_closure_set(x_134, 10, x_127);
lean_closure_set(x_134, 11, x_128);
lean_closure_set(x_134, 12, x_129);
lean_closure_set(x_134, 13, x_2);
lean_closure_set(x_134, 14, x_133);
if (lean_is_scalar(x_110)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_110;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_109);
return x_135;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsync___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsync___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_15);
x_19 = l_Lean_Core_wrapAsync___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_18, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsync___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsync(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4808_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stderrAsMessages", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4808_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4808_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4808_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("server", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4808_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message", 133, 133);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4808_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4808_;
x_2 = l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4808_;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4808_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4808_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_4808_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4808_;
x_3 = l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4808_;
x_4 = l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4808_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_CoreM___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__0____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__1____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__2____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__1____x40_Lean_CoreM___hyg_4846_;
x_2 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4846_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__3____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___auto___closed__4____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto___closed__5____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__4____x40_Lean_CoreM___hyg_4846_;
x_2 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4846_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__6____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__7____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__6____x40_Lean_CoreM___hyg_4846_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__8____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto___closed__9____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__8____x40_Lean_CoreM___hyg_4846_;
x_2 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4846_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__10____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__8____x40_Lean_CoreM___hyg_4846_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__11____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__10____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__12____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__13____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__14____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__13____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__12____x40_Lean_CoreM___hyg_4846_;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4846_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__15____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto___closed__16____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__15____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__12____x40_Lean_CoreM___hyg_4846_;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4846_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__17____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl_name%", 10, 10);
return x_1;
}
}
static lean_object* _init_l___auto___closed__18____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__17____x40_Lean_CoreM___hyg_4846_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__19____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__18____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__20____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__19____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__16____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__21____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__20____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__22____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___auto___closed__23____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__22____x40_Lean_CoreM___hyg_4846_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__24____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__23____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__21____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__25____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toString", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto___closed__26____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__25____x40_Lean_CoreM___hyg_4846_;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__27____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__26____x40_Lean_CoreM___hyg_4846_;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___auto___closed__25____x40_Lean_CoreM___hyg_4846_;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__28____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__25____x40_Lean_CoreM___hyg_4846_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__29____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l___auto___closed__28____x40_Lean_CoreM___hyg_4846_;
x_3 = l___auto___closed__27____x40_Lean_CoreM___hyg_4846_;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__30____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__29____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__24____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__31____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__30____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__14____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__32____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__31____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__11____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__33____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__32____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__9____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__34____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__33____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__35____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__34____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__7____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__36____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__35____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__37____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__36____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__5____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__38____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__37____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__39____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__38____x40_Lean_CoreM___hyg_4846_;
x_2 = l___auto___closed__2____x40_Lean_CoreM___hyg_4846_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_4846_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__39____x40_Lean_CoreM___hyg_4846_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_6 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 6);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 8);
lean_inc_ref(x_8);
lean_dec_ref(x_3);
x_26 = lean_string_utf8_byte_size(x_1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_42; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_2, 5);
lean_inc(x_31);
lean_dec_ref(x_2);
x_42 = l_Lean_Syntax_getPos_x3f(x_31, x_28);
lean_dec(x_31);
if (lean_obj_tag(x_42) == 0)
{
x_32 = x_27;
goto block_41;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_32 = x_43;
goto block_41;
}
block_41:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = l_Lean_FileMap_toPosition(x_30, x_32);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = 0;
x_36 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_1);
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*5, x_28);
lean_ctor_set_uint8(x_39, sizeof(void*)*5 + 1, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*5 + 2, x_28);
x_40 = l_Lean_MessageLog_add(x_39, x_7);
x_9 = x_40;
x_10 = x_5;
goto block_25;
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = x_7;
x_10 = x_5;
goto block_25;
}
block_25:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_6);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_box(0);
x_21 = 0;
x_22 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_6);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_4987_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__39____x40_Lean_CoreM___hyg_4846_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; 
lean_free_object(x_4);
lean_dec(x_7);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0;
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_5);
x_8 = lean_st_ref_take(x_1, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 4);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
lean_ctor_set(x_10, 0, x_16);
x_17 = lean_st_ref_set(x_1, x_9, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_23 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
x_24 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint64(x_24, sizeof(void*)*1, x_22);
lean_ctor_set(x_9, 4, x_24);
x_25 = lean_st_ref_set(x_1, x_9, x_11);
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
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 5);
x_34 = lean_ctor_get(x_9, 6);
x_35 = lean_ctor_get(x_9, 7);
x_36 = lean_ctor_get(x_9, 8);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_37 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_38 = x_10;
} else {
 lean_dec_ref(x_10);
 x_38 = lean_box(0);
}
x_39 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 1, 8);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint64(x_40, sizeof(void*)*1, x_37);
x_41 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_36);
x_42 = lean_st_ref_set(x_1, x_41, x_11);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_7);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_nat_dec_eq(x_10, x_12);
if (x_14 == 0)
{
x_7 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_11, x_13);
x_7 = x_15;
goto block_9;
}
block_9:
{
if (x_7 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_nat_dec_eq(x_9, x_11);
if (x_13 == 0)
{
x_6 = x_13;
goto block_8;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_10, x_12);
x_6 = x_14;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_1);
x_9 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
x_10 = lean_uint64_of_nat(x_7);
lean_dec(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
x_31 = lean_array_get_size(x_1);
x_32 = lean_uint64_of_nat(x_29);
lean_dec(x_29);
x_33 = lean_uint64_of_nat(x_30);
lean_dec(x_30);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_nat_dec_eq(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_8 = x_18;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(1, 3, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(1, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_6);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_8, x_7);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = lean_array_uget(x_6, x_8);
lean_inc(x_16);
x_19 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_2, x_3, x_4, x_18, x_16, x_10, x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_9, 0, x_23);
lean_ctor_set(x_19, 0, x_9);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_9, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec_ref(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec_ref(x_20);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_28);
lean_ctor_set(x_9, 0, x_5);
x_29 = 1;
x_30 = lean_usize_add(x_8, x_29);
x_8 = x_30;
x_12 = x_27;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_dec(x_9);
x_33 = lean_array_uget(x_6, x_8);
lean_inc(x_32);
x_34 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_2, x_3, x_4, x_33, x_32, x_10, x_11, x_12);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
lean_dec(x_32);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec_ref(x_34);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec_ref(x_35);
lean_inc(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_42);
x_44 = 1;
x_45 = lean_usize_add(x_8, x_44);
x_8 = x_45;
x_9 = x_43;
x_12 = x_41;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_106; lean_object* x_107; lean_object* x_111; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec_ref(x_6);
x_18 = lean_ctor_get(x_7, 5);
x_19 = lean_array_uget(x_3, x_5);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_106 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_20);
x_111 = l_Lean_Syntax_getPos_x3f(x_106, x_2);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_unsigned_to_nat(0u);
x_107 = x_112;
goto block_110;
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec_ref(x_111);
x_107 = x_113;
goto block_110;
}
block_105:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
if (lean_is_scalar(x_22)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_22;
}
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0;
x_30 = lean_array_get_size(x_27);
x_31 = lean_uint64_of_nat(x_23);
lean_dec(x_23);
x_32 = lean_uint64_of_nat(x_24);
lean_dec(x_24);
x_33 = lean_uint64_mix_hash(x_31, x_32);
x_34 = 32;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = 16;
x_38 = lean_uint64_shift_right(x_36, x_37);
x_39 = lean_uint64_xor(x_36, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_42 = 1;
x_43 = lean_usize_sub(x_41, x_42);
x_44 = lean_usize_land(x_40, x_43);
x_45 = lean_array_uget(x_27, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_28, x_29, x_45);
x_47 = lean_array_push(x_46, x_21);
x_48 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_28, x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_26, x_49);
lean_dec(x_26);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_28);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_45);
x_52 = lean_array_uset(x_27, x_44, x_51);
x_53 = lean_unsigned_to_nat(4u);
x_54 = lean_nat_mul(x_50, x_53);
x_55 = lean_unsigned_to_nat(3u);
x_56 = lean_nat_div(x_54, x_55);
lean_dec(x_54);
x_57 = lean_array_get_size(x_52);
x_58 = lean_nat_dec_le(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_52);
lean_ctor_set(x_17, 1, x_59);
lean_ctor_set(x_17, 0, x_50);
x_9 = x_17;
goto block_14;
}
else
{
lean_ctor_set(x_17, 1, x_52);
lean_ctor_set(x_17, 0, x_50);
x_9 = x_17;
goto block_14;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_box(0);
x_61 = lean_array_uset(x_27, x_44, x_60);
x_62 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_28, x_47, x_45);
x_63 = lean_array_uset(x_61, x_44, x_62);
lean_ctor_set(x_17, 1, x_63);
x_9 = x_17;
goto block_14;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; size_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_64 = lean_ctor_get(x_17, 0);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_17);
lean_inc(x_24);
lean_inc(x_23);
if (lean_is_scalar(x_22)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_22;
}
lean_ctor_set(x_66, 0, x_23);
lean_ctor_set(x_66, 1, x_24);
x_67 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0;
x_68 = lean_array_get_size(x_65);
x_69 = lean_uint64_of_nat(x_23);
lean_dec(x_23);
x_70 = lean_uint64_of_nat(x_24);
lean_dec(x_24);
x_71 = lean_uint64_mix_hash(x_69, x_70);
x_72 = 32;
x_73 = lean_uint64_shift_right(x_71, x_72);
x_74 = lean_uint64_xor(x_71, x_73);
x_75 = 16;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = lean_uint64_to_usize(x_77);
x_79 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_80 = 1;
x_81 = lean_usize_sub(x_79, x_80);
x_82 = lean_usize_land(x_78, x_81);
x_83 = lean_array_uget(x_65, x_82);
x_84 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_66, x_67, x_83);
x_85 = lean_array_push(x_84, x_21);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_66, x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_64, x_87);
lean_dec(x_64);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_66);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_83);
x_90 = lean_array_uset(x_65, x_82, x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_mul(x_88, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_97);
x_9 = x_98;
goto block_14;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_90);
x_9 = x_99;
goto block_14;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_box(0);
x_101 = lean_array_uset(x_65, x_82, x_100);
x_102 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_66, x_85, x_83);
x_103 = lean_array_uset(x_101, x_82, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_64);
lean_ctor_set(x_104, 1, x_103);
x_9 = x_104;
goto block_14;
}
}
}
block_110:
{
lean_object* x_108; 
x_108 = l_Lean_Syntax_getTailPos_x3f(x_106, x_2);
lean_dec(x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_inc(x_107);
x_23 = x_107;
x_24 = x_107;
goto block_105;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_23 = x_107;
x_24 = x_109;
goto block_105;
}
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_109; lean_object* x_110; lean_object* x_114; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec_ref(x_8);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_array_uget(x_5, x_7);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_109 = l_Lean_replaceRef(x_23, x_21);
lean_dec(x_23);
x_114 = l_Lean_Syntax_getPos_x3f(x_109, x_3);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_unsigned_to_nat(0u);
x_110 = x_115;
goto block_113;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec_ref(x_114);
x_110 = x_116;
goto block_113;
}
block_108:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; size_t x_43; size_t x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
if (lean_is_scalar(x_25)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_25;
}
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
x_32 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0;
x_33 = lean_array_get_size(x_30);
x_34 = lean_uint64_of_nat(x_26);
lean_dec(x_26);
x_35 = lean_uint64_of_nat(x_27);
lean_dec(x_27);
x_36 = lean_uint64_mix_hash(x_34, x_35);
x_37 = 32;
x_38 = lean_uint64_shift_right(x_36, x_37);
x_39 = lean_uint64_xor(x_36, x_38);
x_40 = 16;
x_41 = lean_uint64_shift_right(x_39, x_40);
x_42 = lean_uint64_xor(x_39, x_41);
x_43 = lean_uint64_to_usize(x_42);
x_44 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_45 = 1;
x_46 = lean_usize_sub(x_44, x_45);
x_47 = lean_usize_land(x_43, x_46);
x_48 = lean_array_uget(x_30, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_31, x_32, x_48);
x_50 = lean_array_push(x_49, x_24);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_31, x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_29, x_52);
lean_dec(x_29);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_31);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_48);
x_55 = lean_array_uset(x_30, x_47, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_55);
lean_ctor_set(x_20, 1, x_62);
lean_ctor_set(x_20, 0, x_53);
x_12 = x_20;
goto block_17;
}
else
{
lean_ctor_set(x_20, 1, x_55);
lean_ctor_set(x_20, 0, x_53);
x_12 = x_20;
goto block_17;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_uset(x_30, x_47, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_31, x_50, x_48);
x_66 = lean_array_uset(x_64, x_47, x_65);
lean_ctor_set(x_20, 1, x_66);
x_12 = x_20;
goto block_17;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_67 = lean_ctor_get(x_20, 0);
x_68 = lean_ctor_get(x_20, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_20);
lean_inc(x_27);
lean_inc(x_26);
if (lean_is_scalar(x_25)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_25;
}
lean_ctor_set(x_69, 0, x_26);
lean_ctor_set(x_69, 1, x_27);
x_70 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0;
x_71 = lean_array_get_size(x_68);
x_72 = lean_uint64_of_nat(x_26);
lean_dec(x_26);
x_73 = lean_uint64_of_nat(x_27);
lean_dec(x_27);
x_74 = lean_uint64_mix_hash(x_72, x_73);
x_75 = 32;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = 16;
x_79 = lean_uint64_shift_right(x_77, x_78);
x_80 = lean_uint64_xor(x_77, x_79);
x_81 = lean_uint64_to_usize(x_80);
x_82 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_83 = 1;
x_84 = lean_usize_sub(x_82, x_83);
x_85 = lean_usize_land(x_81, x_84);
x_86 = lean_array_uget(x_68, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_69, x_70, x_86);
x_88 = lean_array_push(x_87, x_24);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_69, x_86);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_67, x_90);
lean_dec(x_67);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_69);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_86);
x_93 = lean_array_uset(x_68, x_85, x_92);
x_94 = lean_unsigned_to_nat(4u);
x_95 = lean_nat_mul(x_91, x_94);
x_96 = lean_unsigned_to_nat(3u);
x_97 = lean_nat_div(x_95, x_96);
lean_dec(x_95);
x_98 = lean_array_get_size(x_93);
x_99 = lean_nat_dec_le(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_100);
x_12 = x_101;
goto block_17;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_93);
x_12 = x_102;
goto block_17;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_box(0);
x_104 = lean_array_uset(x_68, x_85, x_103);
x_105 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_69, x_88, x_86);
x_106 = lean_array_uset(x_104, x_85, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_67);
lean_ctor_set(x_107, 1, x_106);
x_12 = x_107;
goto block_17;
}
}
}
block_113:
{
lean_object* x_111; 
x_111 = l_Lean_Syntax_getTailPos_x3f(x_109, x_3);
lean_dec(x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_inc(x_110);
x_26 = x_110;
x_27 = x_110;
goto block_108;
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_26 = x_110;
x_27 = x_112;
goto block_108;
}
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
lean_inc(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_7, x_14);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(x_4, x_3, x_5, x_6, x_15, x_13, x_9, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_array_size(x_11);
x_15 = 0;
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(x_1, x_2, x_3, x_4, x_12, x_11, x_14, x_15, x_13, x_7, x_8, x_9);
lean_dec_ref(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_21);
lean_ctor_set(x_16, 0, x_5);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_free_object(x_5);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec_ref(x_18);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec_ref(x_18);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_array_size(x_31);
x_35 = 0;
x_36 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(x_1, x_2, x_3, x_4, x_32, x_31, x_34, x_35, x_33, x_7, x_8, x_9);
lean_dec_ref(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_45 = x_36;
} else {
 lean_dec_ref(x_36);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec_ref(x_38);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_5, 0);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
x_52 = lean_array_size(x_49);
x_53 = 0;
x_54 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(x_1, x_2, x_3, x_50, x_49, x_52, x_53, x_51, x_7, x_8, x_9);
lean_dec_ref(x_49);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
lean_ctor_set(x_5, 0, x_59);
lean_ctor_set(x_54, 0, x_5);
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
lean_ctor_set(x_5, 0, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_5);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_55);
lean_free_object(x_5);
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_54, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
lean_dec_ref(x_56);
lean_ctor_set(x_54, 0, x_65);
return x_54;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_dec(x_54);
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec_ref(x_56);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_5, 0);
lean_inc(x_69);
lean_dec(x_5);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_6);
x_72 = lean_array_size(x_69);
x_73 = 0;
x_74 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(x_1, x_2, x_3, x_70, x_69, x_72, x_73, x_71, x_7, x_8, x_9);
lean_dec_ref(x_69);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_75);
x_82 = lean_ctor_get(x_74, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_83 = x_74;
} else {
 lean_dec_ref(x_74);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
lean_dec_ref(x_76);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_106; lean_object* x_107; lean_object* x_111; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec_ref(x_6);
x_18 = lean_ctor_get(x_7, 5);
x_19 = lean_array_uget(x_3, x_5);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_106 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_20);
x_111 = l_Lean_Syntax_getPos_x3f(x_106, x_2);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_unsigned_to_nat(0u);
x_107 = x_112;
goto block_110;
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec_ref(x_111);
x_107 = x_113;
goto block_110;
}
block_105:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
if (lean_is_scalar(x_22)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_22;
}
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0;
x_30 = lean_array_get_size(x_27);
x_31 = lean_uint64_of_nat(x_23);
lean_dec(x_23);
x_32 = lean_uint64_of_nat(x_24);
lean_dec(x_24);
x_33 = lean_uint64_mix_hash(x_31, x_32);
x_34 = 32;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = 16;
x_38 = lean_uint64_shift_right(x_36, x_37);
x_39 = lean_uint64_xor(x_36, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_42 = 1;
x_43 = lean_usize_sub(x_41, x_42);
x_44 = lean_usize_land(x_40, x_43);
x_45 = lean_array_uget(x_27, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_28, x_29, x_45);
x_47 = lean_array_push(x_46, x_21);
x_48 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_28, x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_26, x_49);
lean_dec(x_26);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_28);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_45);
x_52 = lean_array_uset(x_27, x_44, x_51);
x_53 = lean_unsigned_to_nat(4u);
x_54 = lean_nat_mul(x_50, x_53);
x_55 = lean_unsigned_to_nat(3u);
x_56 = lean_nat_div(x_54, x_55);
lean_dec(x_54);
x_57 = lean_array_get_size(x_52);
x_58 = lean_nat_dec_le(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_52);
lean_ctor_set(x_17, 1, x_59);
lean_ctor_set(x_17, 0, x_50);
x_9 = x_17;
goto block_14;
}
else
{
lean_ctor_set(x_17, 1, x_52);
lean_ctor_set(x_17, 0, x_50);
x_9 = x_17;
goto block_14;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_box(0);
x_61 = lean_array_uset(x_27, x_44, x_60);
x_62 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_28, x_47, x_45);
x_63 = lean_array_uset(x_61, x_44, x_62);
lean_ctor_set(x_17, 1, x_63);
x_9 = x_17;
goto block_14;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; size_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_64 = lean_ctor_get(x_17, 0);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_17);
lean_inc(x_24);
lean_inc(x_23);
if (lean_is_scalar(x_22)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_22;
}
lean_ctor_set(x_66, 0, x_23);
lean_ctor_set(x_66, 1, x_24);
x_67 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0;
x_68 = lean_array_get_size(x_65);
x_69 = lean_uint64_of_nat(x_23);
lean_dec(x_23);
x_70 = lean_uint64_of_nat(x_24);
lean_dec(x_24);
x_71 = lean_uint64_mix_hash(x_69, x_70);
x_72 = 32;
x_73 = lean_uint64_shift_right(x_71, x_72);
x_74 = lean_uint64_xor(x_71, x_73);
x_75 = 16;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = lean_uint64_to_usize(x_77);
x_79 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_80 = 1;
x_81 = lean_usize_sub(x_79, x_80);
x_82 = lean_usize_land(x_78, x_81);
x_83 = lean_array_uget(x_65, x_82);
x_84 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_66, x_67, x_83);
x_85 = lean_array_push(x_84, x_21);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_66, x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_64, x_87);
lean_dec(x_64);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_66);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_83);
x_90 = lean_array_uset(x_65, x_82, x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_mul(x_88, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_97);
x_9 = x_98;
goto block_14;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_90);
x_9 = x_99;
goto block_14;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_box(0);
x_101 = lean_array_uset(x_65, x_82, x_100);
x_102 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_66, x_85, x_83);
x_103 = lean_array_uset(x_101, x_82, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_64);
lean_ctor_set(x_104, 1, x_103);
x_9 = x_104;
goto block_14;
}
}
}
block_110:
{
lean_object* x_108; 
x_108 = l_Lean_Syntax_getTailPos_x3f(x_106, x_2);
lean_dec(x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_inc(x_107);
x_23 = x_107;
x_24 = x_107;
goto block_105;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_23 = x_107;
x_24 = x_109;
goto block_105;
}
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_109; lean_object* x_110; lean_object* x_114; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec_ref(x_8);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_array_uget(x_5, x_7);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_109 = l_Lean_replaceRef(x_23, x_21);
lean_dec(x_23);
x_114 = l_Lean_Syntax_getPos_x3f(x_109, x_3);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_unsigned_to_nat(0u);
x_110 = x_115;
goto block_113;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec_ref(x_114);
x_110 = x_116;
goto block_113;
}
block_108:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; size_t x_43; size_t x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
if (lean_is_scalar(x_25)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_25;
}
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
x_32 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0;
x_33 = lean_array_get_size(x_30);
x_34 = lean_uint64_of_nat(x_26);
lean_dec(x_26);
x_35 = lean_uint64_of_nat(x_27);
lean_dec(x_27);
x_36 = lean_uint64_mix_hash(x_34, x_35);
x_37 = 32;
x_38 = lean_uint64_shift_right(x_36, x_37);
x_39 = lean_uint64_xor(x_36, x_38);
x_40 = 16;
x_41 = lean_uint64_shift_right(x_39, x_40);
x_42 = lean_uint64_xor(x_39, x_41);
x_43 = lean_uint64_to_usize(x_42);
x_44 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_45 = 1;
x_46 = lean_usize_sub(x_44, x_45);
x_47 = lean_usize_land(x_43, x_46);
x_48 = lean_array_uget(x_30, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_31, x_32, x_48);
x_50 = lean_array_push(x_49, x_24);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_31, x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_29, x_52);
lean_dec(x_29);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_31);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_48);
x_55 = lean_array_uset(x_30, x_47, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_55);
lean_ctor_set(x_20, 1, x_62);
lean_ctor_set(x_20, 0, x_53);
x_12 = x_20;
goto block_17;
}
else
{
lean_ctor_set(x_20, 1, x_55);
lean_ctor_set(x_20, 0, x_53);
x_12 = x_20;
goto block_17;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_uset(x_30, x_47, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_31, x_50, x_48);
x_66 = lean_array_uset(x_64, x_47, x_65);
lean_ctor_set(x_20, 1, x_66);
x_12 = x_20;
goto block_17;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_67 = lean_ctor_get(x_20, 0);
x_68 = lean_ctor_get(x_20, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_20);
lean_inc(x_27);
lean_inc(x_26);
if (lean_is_scalar(x_25)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_25;
}
lean_ctor_set(x_69, 0, x_26);
lean_ctor_set(x_69, 1, x_27);
x_70 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0;
x_71 = lean_array_get_size(x_68);
x_72 = lean_uint64_of_nat(x_26);
lean_dec(x_26);
x_73 = lean_uint64_of_nat(x_27);
lean_dec(x_27);
x_74 = lean_uint64_mix_hash(x_72, x_73);
x_75 = 32;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = 16;
x_79 = lean_uint64_shift_right(x_77, x_78);
x_80 = lean_uint64_xor(x_77, x_79);
x_81 = lean_uint64_to_usize(x_80);
x_82 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_83 = 1;
x_84 = lean_usize_sub(x_82, x_83);
x_85 = lean_usize_land(x_81, x_84);
x_86 = lean_array_uget(x_68, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_69, x_70, x_86);
x_88 = lean_array_push(x_87, x_24);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_69, x_86);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_67, x_90);
lean_dec(x_67);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_69);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_86);
x_93 = lean_array_uset(x_68, x_85, x_92);
x_94 = lean_unsigned_to_nat(4u);
x_95 = lean_nat_mul(x_91, x_94);
x_96 = lean_unsigned_to_nat(3u);
x_97 = lean_nat_div(x_95, x_96);
lean_dec(x_95);
x_98 = lean_array_get_size(x_93);
x_99 = lean_nat_dec_le(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_100);
x_12 = x_101;
goto block_17;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_93);
x_12 = x_102;
goto block_17;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_box(0);
x_104 = lean_array_uset(x_68, x_85, x_103);
x_105 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_69, x_88, x_86);
x_106 = lean_array_uset(x_104, x_85, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_67);
lean_ctor_set(x_107, 1, x_106);
x_12 = x_107;
goto block_17;
}
}
}
block_113:
{
lean_object* x_111; 
x_111 = l_Lean_Syntax_getTailPos_x3f(x_109, x_3);
lean_dec(x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_inc(x_110);
x_26 = x_110;
x_27 = x_110;
goto block_108;
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_26 = x_110;
x_27 = x_112;
goto block_108;
}
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
lean_inc(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_7, x_14);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(x_4, x_3, x_5, x_6, x_15, x_13, x_9, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_4);
lean_inc_ref(x_5);
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_2, x_3, x_5, x_9, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec_ref(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec_ref(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_size(x_10);
x_24 = 0;
x_25 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12(x_1, x_2, x_3, x_21, x_10, x_23, x_24, x_22, x_6, x_7, x_19);
lean_dec_ref(x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_26);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec_ref(x_27);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec_ref(x_27);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_string_dec_eq(x_6, x_1);
if (x_7 == 0)
{
return x_2;
}
else
{
return x_3;
}
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_5, 1);
x_11 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
x_14 = lean_string_dec_eq(x_10, x_13);
if (x_14 == 0)
{
return x_2;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__2;
x_16 = lean_string_dec_eq(x_9, x_15);
if (x_16 == 0)
{
return x_2;
}
else
{
return x_3;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__3;
x_18 = lean_string_dec_eq(x_9, x_17);
if (x_18 == 0)
{
return x_2;
}
else
{
return x_3;
}
}
}
else
{
return x_2;
}
}
default: 
{
return x_2;
}
}
}
else
{
return x_2;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_nil;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_8);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; double x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
x_26 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_29 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
x_30 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__0;
x_31 = lean_box(0);
lean_inc(x_1);
x_32 = lean_float_of_nat(x_1);
x_33 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_34 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_float(x_34, sizeof(void*)*2, x_32);
lean_ctor_set_float(x_34, sizeof(void*)*2 + 8, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 16, x_17);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__1;
x_36 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set_tag(x_20, 8);
lean_ctor_set(x_20, 1, x_36);
lean_ctor_set(x_20, 0, x_30);
x_37 = 0;
x_38 = l_Lean_Elab_mkMessageCore(x_26, x_27, x_20, x_37, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_28 == 0)
{
lean_inc_ref(x_8);
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
goto block_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_38, 4);
lean_inc(x_129);
x_130 = lean_box(x_3);
x_131 = lean_box(x_28);
x_132 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0___boxed), 4, 3);
lean_closure_set(x_132, 0, x_29);
lean_closure_set(x_132, 1, x_130);
lean_closure_set(x_132, 2, x_131);
x_133 = l_Lean_MessageData_hasTag(x_132, x_129);
if (x_133 == 0)
{
lean_dec_ref(x_38);
lean_dec(x_22);
x_11 = x_2;
x_12 = x_10;
goto block_16;
}
else
{
lean_inc_ref(x_8);
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
goto block_128;
}
}
block_128:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_st_ref_take(x_40, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_38, 4);
x_48 = lean_ctor_get(x_39, 6);
lean_inc(x_48);
x_49 = lean_ctor_get(x_39, 7);
lean_inc(x_49);
lean_dec_ref(x_39);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_45, 6);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_42, 0, x_48);
if (lean_is_scalar(x_22)) {
 x_52 = lean_alloc_ctor(4, 2, 0);
} else {
 x_52 = x_22;
 lean_ctor_set_tag(x_52, 4);
}
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_38, 4, x_52);
x_53 = l_Lean_MessageLog_add(x_38, x_51);
lean_ctor_set(x_45, 6, x_53);
x_54 = lean_st_ref_set(x_40, x_45, x_46);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_11 = x_2;
x_12 = x_55;
goto block_16;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_45, 0);
x_57 = lean_ctor_get(x_45, 1);
x_58 = lean_ctor_get(x_45, 2);
x_59 = lean_ctor_get(x_45, 3);
x_60 = lean_ctor_get(x_45, 4);
x_61 = lean_ctor_get(x_45, 5);
x_62 = lean_ctor_get(x_45, 6);
x_63 = lean_ctor_get(x_45, 7);
x_64 = lean_ctor_get(x_45, 8);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_45);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_42, 0, x_48);
if (lean_is_scalar(x_22)) {
 x_65 = lean_alloc_ctor(4, 2, 0);
} else {
 x_65 = x_22;
 lean_ctor_set_tag(x_65, 4);
}
lean_ctor_set(x_65, 0, x_42);
lean_ctor_set(x_65, 1, x_47);
lean_ctor_set(x_38, 4, x_65);
x_66 = l_Lean_MessageLog_add(x_38, x_62);
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_57);
lean_ctor_set(x_67, 2, x_58);
lean_ctor_set(x_67, 3, x_59);
lean_ctor_set(x_67, 4, x_60);
lean_ctor_set(x_67, 5, x_61);
lean_ctor_set(x_67, 6, x_66);
lean_ctor_set(x_67, 7, x_63);
lean_ctor_set(x_67, 8, x_64);
x_68 = lean_st_ref_set(x_40, x_67, x_46);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_11 = x_2;
x_12 = x_69;
goto block_16;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_70 = lean_ctor_get(x_42, 0);
x_71 = lean_ctor_get(x_42, 1);
x_72 = lean_ctor_get(x_38, 0);
x_73 = lean_ctor_get(x_38, 1);
x_74 = lean_ctor_get(x_38, 2);
x_75 = lean_ctor_get_uint8(x_38, sizeof(void*)*5);
x_76 = lean_ctor_get_uint8(x_38, sizeof(void*)*5 + 1);
x_77 = lean_ctor_get_uint8(x_38, sizeof(void*)*5 + 2);
x_78 = lean_ctor_get(x_38, 3);
x_79 = lean_ctor_get(x_38, 4);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_38);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
x_81 = lean_ctor_get(x_39, 7);
lean_inc(x_81);
lean_dec_ref(x_39);
x_82 = lean_ctor_get(x_70, 0);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_70, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_70, 2);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_70, 3);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_70, 4);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_70, 5);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_70, 6);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_70, 7);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_70, 8);
lean_inc_ref(x_90);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 lean_ctor_release(x_70, 6);
 lean_ctor_release(x_70, 7);
 lean_ctor_release(x_70, 8);
 x_91 = x_70;
} else {
 lean_dec_ref(x_70);
 x_91 = lean_box(0);
}
lean_ctor_set(x_42, 1, x_81);
lean_ctor_set(x_42, 0, x_80);
if (lean_is_scalar(x_22)) {
 x_92 = lean_alloc_ctor(4, 2, 0);
} else {
 x_92 = x_22;
 lean_ctor_set_tag(x_92, 4);
}
lean_ctor_set(x_92, 0, x_42);
lean_ctor_set(x_92, 1, x_79);
x_93 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_93, 0, x_72);
lean_ctor_set(x_93, 1, x_73);
lean_ctor_set(x_93, 2, x_74);
lean_ctor_set(x_93, 3, x_78);
lean_ctor_set(x_93, 4, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*5, x_75);
lean_ctor_set_uint8(x_93, sizeof(void*)*5 + 1, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*5 + 2, x_77);
x_94 = l_Lean_MessageLog_add(x_93, x_88);
if (lean_is_scalar(x_91)) {
 x_95 = lean_alloc_ctor(0, 9, 0);
} else {
 x_95 = x_91;
}
lean_ctor_set(x_95, 0, x_82);
lean_ctor_set(x_95, 1, x_83);
lean_ctor_set(x_95, 2, x_84);
lean_ctor_set(x_95, 3, x_85);
lean_ctor_set(x_95, 4, x_86);
lean_ctor_set(x_95, 5, x_87);
lean_ctor_set(x_95, 6, x_94);
lean_ctor_set(x_95, 7, x_89);
lean_ctor_set(x_95, 8, x_90);
x_96 = lean_st_ref_set(x_40, x_95, x_71);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec_ref(x_96);
x_11 = x_2;
x_12 = x_97;
goto block_16;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_98 = lean_ctor_get(x_42, 0);
x_99 = lean_ctor_get(x_42, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_42);
x_100 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_38, 1);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_38, 2);
lean_inc(x_102);
x_103 = lean_ctor_get_uint8(x_38, sizeof(void*)*5);
x_104 = lean_ctor_get_uint8(x_38, sizeof(void*)*5 + 1);
x_105 = lean_ctor_get_uint8(x_38, sizeof(void*)*5 + 2);
x_106 = lean_ctor_get(x_38, 3);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_38, 4);
lean_inc(x_107);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 x_108 = x_38;
} else {
 lean_dec_ref(x_38);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_39, 6);
lean_inc(x_109);
x_110 = lean_ctor_get(x_39, 7);
lean_inc(x_110);
lean_dec_ref(x_39);
x_111 = lean_ctor_get(x_98, 0);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_98, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_98, 2);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_98, 3);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_98, 4);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_98, 5);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_98, 6);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_98, 7);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_98, 8);
lean_inc_ref(x_119);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 lean_ctor_release(x_98, 2);
 lean_ctor_release(x_98, 3);
 lean_ctor_release(x_98, 4);
 lean_ctor_release(x_98, 5);
 lean_ctor_release(x_98, 6);
 lean_ctor_release(x_98, 7);
 lean_ctor_release(x_98, 8);
 x_120 = x_98;
} else {
 lean_dec_ref(x_98);
 x_120 = lean_box(0);
}
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_109);
lean_ctor_set(x_121, 1, x_110);
if (lean_is_scalar(x_22)) {
 x_122 = lean_alloc_ctor(4, 2, 0);
} else {
 x_122 = x_22;
 lean_ctor_set_tag(x_122, 4);
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_107);
if (lean_is_scalar(x_108)) {
 x_123 = lean_alloc_ctor(0, 5, 3);
} else {
 x_123 = x_108;
}
lean_ctor_set(x_123, 0, x_100);
lean_ctor_set(x_123, 1, x_101);
lean_ctor_set(x_123, 2, x_102);
lean_ctor_set(x_123, 3, x_106);
lean_ctor_set(x_123, 4, x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*5, x_103);
lean_ctor_set_uint8(x_123, sizeof(void*)*5 + 1, x_104);
lean_ctor_set_uint8(x_123, sizeof(void*)*5 + 2, x_105);
x_124 = l_Lean_MessageLog_add(x_123, x_117);
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(0, 9, 0);
} else {
 x_125 = x_120;
}
lean_ctor_set(x_125, 0, x_111);
lean_ctor_set(x_125, 1, x_112);
lean_ctor_set(x_125, 2, x_113);
lean_ctor_set(x_125, 3, x_114);
lean_ctor_set(x_125, 4, x_115);
lean_ctor_set(x_125, 5, x_116);
lean_ctor_set(x_125, 6, x_124);
lean_ctor_set(x_125, 7, x_118);
lean_ctor_set(x_125, 8, x_119);
x_126 = lean_st_ref_set(x_40, x_125, x_99);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
x_11 = x_2;
x_12 = x_127;
goto block_16;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; double x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_134 = lean_ctor_get(x_20, 0);
x_135 = lean_ctor_get(x_20, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_20);
x_136 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_137);
x_138 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_139 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
x_140 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__0;
x_141 = lean_box(0);
lean_inc(x_1);
x_142 = lean_float_of_nat(x_1);
x_143 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_144 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set_float(x_144, sizeof(void*)*2, x_142);
lean_ctor_set_float(x_144, sizeof(void*)*2 + 8, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 16, x_17);
x_145 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__1;
x_146 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_21);
x_147 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_147, 0, x_140);
lean_ctor_set(x_147, 1, x_146);
x_148 = 0;
x_149 = l_Lean_Elab_mkMessageCore(x_136, x_137, x_147, x_148, x_134, x_135);
lean_dec(x_135);
lean_dec(x_134);
if (x_138 == 0)
{
lean_inc_ref(x_8);
x_150 = x_8;
x_151 = x_9;
x_152 = x_10;
goto block_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_186 = lean_ctor_get(x_149, 4);
lean_inc(x_186);
x_187 = lean_box(x_3);
x_188 = lean_box(x_138);
x_189 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0___boxed), 4, 3);
lean_closure_set(x_189, 0, x_139);
lean_closure_set(x_189, 1, x_187);
lean_closure_set(x_189, 2, x_188);
x_190 = l_Lean_MessageData_hasTag(x_189, x_186);
if (x_190 == 0)
{
lean_dec_ref(x_149);
lean_dec(x_22);
x_11 = x_2;
x_12 = x_10;
goto block_16;
}
else
{
lean_inc_ref(x_8);
x_150 = x_8;
x_151 = x_9;
x_152 = x_10;
goto block_185;
}
}
block_185:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_153 = lean_st_ref_take(x_151, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_158);
x_159 = lean_ctor_get(x_149, 2);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_149, sizeof(void*)*5);
x_161 = lean_ctor_get_uint8(x_149, sizeof(void*)*5 + 1);
x_162 = lean_ctor_get_uint8(x_149, sizeof(void*)*5 + 2);
x_163 = lean_ctor_get(x_149, 3);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_149, 4);
lean_inc(x_164);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 lean_ctor_release(x_149, 4);
 x_165 = x_149;
} else {
 lean_dec_ref(x_149);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_150, 6);
lean_inc(x_166);
x_167 = lean_ctor_get(x_150, 7);
lean_inc(x_167);
lean_dec_ref(x_150);
x_168 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_154, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_154, 2);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_154, 3);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_154, 4);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_154, 5);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_154, 6);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_154, 7);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_154, 8);
lean_inc_ref(x_176);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 lean_ctor_release(x_154, 5);
 lean_ctor_release(x_154, 6);
 lean_ctor_release(x_154, 7);
 lean_ctor_release(x_154, 8);
 x_177 = x_154;
} else {
 lean_dec_ref(x_154);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_156;
}
lean_ctor_set(x_178, 0, x_166);
lean_ctor_set(x_178, 1, x_167);
if (lean_is_scalar(x_22)) {
 x_179 = lean_alloc_ctor(4, 2, 0);
} else {
 x_179 = x_22;
 lean_ctor_set_tag(x_179, 4);
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_164);
if (lean_is_scalar(x_165)) {
 x_180 = lean_alloc_ctor(0, 5, 3);
} else {
 x_180 = x_165;
}
lean_ctor_set(x_180, 0, x_157);
lean_ctor_set(x_180, 1, x_158);
lean_ctor_set(x_180, 2, x_159);
lean_ctor_set(x_180, 3, x_163);
lean_ctor_set(x_180, 4, x_179);
lean_ctor_set_uint8(x_180, sizeof(void*)*5, x_160);
lean_ctor_set_uint8(x_180, sizeof(void*)*5 + 1, x_161);
lean_ctor_set_uint8(x_180, sizeof(void*)*5 + 2, x_162);
x_181 = l_Lean_MessageLog_add(x_180, x_174);
if (lean_is_scalar(x_177)) {
 x_182 = lean_alloc_ctor(0, 9, 0);
} else {
 x_182 = x_177;
}
lean_ctor_set(x_182, 0, x_168);
lean_ctor_set(x_182, 1, x_169);
lean_ctor_set(x_182, 2, x_170);
lean_ctor_set(x_182, 3, x_171);
lean_ctor_set(x_182, 4, x_172);
lean_ctor_set(x_182, 5, x_173);
lean_ctor_set(x_182, 6, x_181);
lean_ctor_set(x_182, 7, x_175);
lean_ctor_set(x_182, 8, x_176);
x_183 = lean_st_ref_set(x_151, x_182, x_155);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec_ref(x_183);
x_11 = x_2;
x_12 = x_184;
goto block_16;
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
x_7 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_nat_dec_lt(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_output;
return x_1;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instHashablePos___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqPos___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__3;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__5;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__6;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__7;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0;
x_6 = l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(x_4, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_PersistentArray_isEmpty___redArg(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_41; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_free_object(x_7);
x_12 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2;
x_13 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9;
x_16 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(x_13, x_12, x_11, x_9, x_15, x_1, x_2, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_49);
lean_dec(x_17);
x_50 = lean_mk_empty_array_with_capacity(x_48);
lean_dec(x_48);
x_51 = lean_array_get_size(x_49);
x_52 = lean_nat_dec_lt(x_14, x_51);
if (x_52 == 0)
{
lean_dec(x_51);
lean_dec_ref(x_49);
x_41 = x_50;
goto block_47;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_51, x_51);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec_ref(x_49);
x_41 = x_50;
goto block_47;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_56 = l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(x_49, x_54, x_55, x_50);
lean_dec_ref(x_49);
x_41 = x_56;
goto block_47;
}
}
block_28:
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_box(0);
x_21 = lean_array_size(x_19);
x_22 = 0;
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(x_14, x_20, x_11, x_19, x_21, x_22, x_20, x_1, x_2, x_18);
lean_dec_ref(x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
block_34:
{
lean_object* x_33; 
lean_dec(x_31);
x_33 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_29, x_30, x_32);
lean_dec(x_32);
x_19 = x_33;
goto block_28;
}
block_40:
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_38, x_37);
if (x_39 == 0)
{
lean_dec(x_37);
lean_inc(x_38);
x_29 = x_35;
x_30 = x_38;
x_31 = x_36;
x_32 = x_38;
goto block_34;
}
else
{
x_29 = x_35;
x_30 = x_38;
x_31 = x_36;
x_32 = x_37;
goto block_34;
}
}
block_47:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_array_get_size(x_41);
x_43 = lean_nat_dec_eq(x_42, x_14);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_42, x_44);
x_46 = lean_nat_dec_le(x_14, x_45);
if (x_46 == 0)
{
lean_inc(x_45);
x_35 = x_41;
x_36 = x_42;
x_37 = x_45;
x_38 = x_45;
goto block_40;
}
else
{
x_35 = x_41;
x_36 = x_42;
x_37 = x_45;
x_38 = x_14;
goto block_40;
}
}
else
{
lean_dec(x_42);
x_19 = x_41;
goto block_28;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_9);
lean_dec_ref(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_7, 0, x_57);
return x_7;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_7, 0);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_7);
x_60 = l_Lean_PersistentArray_isEmpty___redArg(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_89; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_61 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2;
x_62 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4;
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9;
x_65 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(x_62, x_61, x_60, x_58, x_64, x_1, x_2, x_59);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_96 = lean_ctor_get(x_66, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_97);
lean_dec(x_66);
x_98 = lean_mk_empty_array_with_capacity(x_96);
lean_dec(x_96);
x_99 = lean_array_get_size(x_97);
x_100 = lean_nat_dec_lt(x_63, x_99);
if (x_100 == 0)
{
lean_dec(x_99);
lean_dec_ref(x_97);
x_89 = x_98;
goto block_95;
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_99, x_99);
if (x_101 == 0)
{
lean_dec(x_99);
lean_dec_ref(x_97);
x_89 = x_98;
goto block_95;
}
else
{
size_t x_102; size_t x_103; lean_object* x_104; 
x_102 = 0;
x_103 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_104 = l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(x_97, x_102, x_103, x_98);
lean_dec_ref(x_97);
x_89 = x_104;
goto block_95;
}
}
block_76:
{
lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_box(0);
x_70 = lean_array_size(x_68);
x_71 = 0;
x_72 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(x_63, x_69, x_60, x_68, x_70, x_71, x_69, x_1, x_2, x_67);
lean_dec_ref(x_68);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
block_82:
{
lean_object* x_81; 
lean_dec(x_79);
x_81 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_77, x_78, x_80);
lean_dec(x_80);
x_68 = x_81;
goto block_76;
}
block_88:
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_86, x_85);
if (x_87 == 0)
{
lean_dec(x_85);
lean_inc(x_86);
x_77 = x_83;
x_78 = x_86;
x_79 = x_84;
x_80 = x_86;
goto block_82;
}
else
{
x_77 = x_83;
x_78 = x_86;
x_79 = x_84;
x_80 = x_85;
goto block_82;
}
}
block_95:
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_array_get_size(x_89);
x_91 = lean_nat_dec_eq(x_90, x_63);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_sub(x_90, x_92);
x_94 = lean_nat_dec_le(x_63, x_93);
if (x_94 == 0)
{
lean_inc(x_93);
x_83 = x_89;
x_84 = x_90;
x_85 = x_93;
x_86 = x_93;
goto block_88;
}
else
{
x_83 = x_89;
x_84 = x_90;
x_85 = x_93;
x_86 = x_63;
goto block_88;
}
}
else
{
lean_dec(x_90);
x_68 = x_89;
goto block_76;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_58);
lean_dec_ref(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_59);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_3);
return x_108;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 12);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = lean_ctor_get(x_5, 5);
x_10 = lean_st_ref_get(x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 4);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_replaceRef(x_3, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_15);
x_16 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(x_17, x_18, x_16);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_20, x_5, x_6, x_13);
lean_dec_ref(x_5);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_st_ref_take(x_6, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_26);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_24, 1);
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_25, 4);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_26, 0);
lean_dec(x_33);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 0, x_3);
x_34 = l_Lean_PersistentArray_push___redArg(x_1, x_24);
lean_ctor_set(x_26, 0, x_34);
x_35 = lean_st_ref_set(x_6, x_25, x_28);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint64_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
lean_dec(x_26);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 0, x_3);
x_43 = l_Lean_PersistentArray_push___redArg(x_1, x_24);
x_44 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint64(x_44, sizeof(void*)*1, x_42);
lean_ctor_set(x_25, 4, x_44);
x_45 = lean_st_ref_set(x_6, x_25, x_28);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 1);
x_52 = lean_ctor_get(x_25, 2);
x_53 = lean_ctor_get(x_25, 3);
x_54 = lean_ctor_get(x_25, 5);
x_55 = lean_ctor_get(x_25, 6);
x_56 = lean_ctor_get(x_25, 7);
x_57 = lean_ctor_get(x_25, 8);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
x_58 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_59 = x_26;
} else {
 lean_dec_ref(x_26);
 x_59 = lean_box(0);
}
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 0, x_3);
x_60 = l_Lean_PersistentArray_push___redArg(x_1, x_24);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 1, 8);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint64(x_61, sizeof(void*)*1, x_58);
x_62 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_52);
lean_ctor_set(x_62, 3, x_53);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_54);
lean_ctor_set(x_62, 6, x_55);
lean_ctor_set(x_62, 7, x_56);
lean_ctor_set(x_62, 8, x_57);
x_63 = lean_st_ref_set(x_6, x_62, x_28);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint64_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_68 = lean_ctor_get(x_24, 1);
lean_inc(x_68);
lean_dec(x_24);
x_69 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_25, 5);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_25, 6);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_25, 7);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_25, 8);
lean_inc_ref(x_76);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 lean_ctor_release(x_25, 7);
 lean_ctor_release(x_25, 8);
 x_77 = x_25;
} else {
 lean_dec_ref(x_25);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_79 = x_26;
} else {
 lean_dec_ref(x_26);
 x_79 = lean_box(0);
}
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_3);
lean_ctor_set(x_80, 1, x_22);
x_81 = l_Lean_PersistentArray_push___redArg(x_1, x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 1, 8);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint64(x_82, sizeof(void*)*1, x_78);
if (lean_is_scalar(x_77)) {
 x_83 = lean_alloc_ctor(0, 9, 0);
} else {
 x_83 = x_77;
}
lean_ctor_set(x_83, 0, x_69);
lean_ctor_set(x_83, 1, x_70);
lean_ctor_set(x_83, 2, x_71);
lean_ctor_set(x_83, 3, x_72);
lean_ctor_set(x_83, 4, x_82);
lean_ctor_set(x_83, 5, x_73);
lean_ctor_set(x_83, 6, x_74);
lean_ctor_set(x_83, 7, x_75);
lean_ctor_set(x_83, 8, x_76);
x_84 = lean_st_ref_set(x_6, x_83, x_68);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint64_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_89 = lean_ctor_get(x_5, 0);
x_90 = lean_ctor_get(x_5, 1);
x_91 = lean_ctor_get(x_5, 2);
x_92 = lean_ctor_get(x_5, 3);
x_93 = lean_ctor_get(x_5, 4);
x_94 = lean_ctor_get(x_5, 5);
x_95 = lean_ctor_get(x_5, 6);
x_96 = lean_ctor_get(x_5, 7);
x_97 = lean_ctor_get(x_5, 8);
x_98 = lean_ctor_get(x_5, 9);
x_99 = lean_ctor_get(x_5, 10);
x_100 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_101 = lean_ctor_get(x_5, 11);
x_102 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_103 = lean_ctor_get(x_5, 12);
lean_inc(x_103);
lean_inc(x_101);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_5);
x_104 = lean_st_ref_get(x_6, x_7);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_105, 4);
lean_inc_ref(x_106);
lean_dec(x_105);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec_ref(x_104);
x_108 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_108);
lean_dec_ref(x_106);
x_109 = l_Lean_replaceRef(x_3, x_94);
lean_dec(x_94);
x_110 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_110, 0, x_89);
lean_ctor_set(x_110, 1, x_90);
lean_ctor_set(x_110, 2, x_91);
lean_ctor_set(x_110, 3, x_92);
lean_ctor_set(x_110, 4, x_93);
lean_ctor_set(x_110, 5, x_109);
lean_ctor_set(x_110, 6, x_95);
lean_ctor_set(x_110, 7, x_96);
lean_ctor_set(x_110, 8, x_97);
lean_ctor_set(x_110, 9, x_98);
lean_ctor_set(x_110, 10, x_99);
lean_ctor_set(x_110, 11, x_101);
lean_ctor_set(x_110, 12, x_103);
lean_ctor_set_uint8(x_110, sizeof(void*)*13, x_100);
lean_ctor_set_uint8(x_110, sizeof(void*)*13 + 1, x_102);
x_111 = l_Lean_PersistentArray_toArray___redArg(x_108);
lean_dec_ref(x_108);
x_112 = lean_array_size(x_111);
x_113 = 0;
x_114 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(x_112, x_113, x_111);
x_115 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_115, 0, x_2);
lean_ctor_set(x_115, 1, x_4);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_115, x_110, x_6, x_107);
lean_dec_ref(x_110);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = lean_st_ref_take(x_6, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_120, 4);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_123 = x_119;
} else {
 lean_dec_ref(x_119);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 2);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_120, 3);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_120, 5);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_120, 6);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_120, 7);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_120, 8);
lean_inc_ref(x_131);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 lean_ctor_release(x_120, 5);
 lean_ctor_release(x_120, 6);
 lean_ctor_release(x_120, 7);
 lean_ctor_release(x_120, 8);
 x_132 = x_120;
} else {
 lean_dec_ref(x_120);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get_uint64(x_121, sizeof(void*)*1);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_134 = x_121;
} else {
 lean_dec_ref(x_121);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_123;
}
lean_ctor_set(x_135, 0, x_3);
lean_ctor_set(x_135, 1, x_117);
x_136 = l_Lean_PersistentArray_push___redArg(x_1, x_135);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(0, 1, 8);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set_uint64(x_137, sizeof(void*)*1, x_133);
if (lean_is_scalar(x_132)) {
 x_138 = lean_alloc_ctor(0, 9, 0);
} else {
 x_138 = x_132;
}
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_125);
lean_ctor_set(x_138, 2, x_126);
lean_ctor_set(x_138, 3, x_127);
lean_ctor_set(x_138, 4, x_137);
lean_ctor_set(x_138, 5, x_128);
lean_ctor_set(x_138, 6, x_129);
lean_ctor_set(x_138, 7, x_130);
lean_ctor_set(x_138, 8, x_131);
x_139 = lean_st_ref_set(x_6, x_138, x_122);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
x_142 = lean_box(0);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21(x_1, x_5, x_2, x_3, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_4, x_11);
return x_12;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__5() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__6() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHeartbeats;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; double x_14; double x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; double x_30; double x_31; lean_object* x_32; lean_object* x_43; lean_object* x_44; double x_45; uint8_t x_46; double x_47; lean_object* x_48; lean_object* x_49; lean_object* x_58; lean_object* x_59; uint8_t x_60; double x_61; lean_object* x_62; lean_object* x_63; double x_64; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; double x_83; double x_84; lean_object* x_85; uint8_t x_86; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; double x_130; double x_131; lean_object* x_132; double x_133; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_159; lean_object* x_160; double x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; double x_166; uint8_t x_167; lean_object* x_206; lean_object* x_207; uint8_t x_208; double x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; double x_213; double x_214; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_269; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 5);
lean_inc(x_10);
lean_inc(x_1);
x_75 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_1, x_6, x_8);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_269 = lean_unbox(x_76);
if (x_269 == 0)
{
lean_object* x_270; uint8_t x_271; 
x_270 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__3;
x_271 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_9, x_270);
if (x_271 == 0)
{
lean_object* x_272; 
lean_dec(x_76);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_272 = lean_apply_3(x_3, x_6, x_7, x_77);
return x_272;
}
else
{
goto block_268;
}
}
else
{
goto block_268;
}
block_25:
{
if (x_13 == 0)
{
double x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__0;
x_19 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set_float(x_19, sizeof(void*)*2, x_18);
lean_ctor_set_float(x_19, sizeof(void*)*2 + 8, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_4);
x_20 = lean_box(0);
x_21 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(x_11, x_10, x_16, x_12, x_19, x_20, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec_ref(x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set_float(x_22, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_22, sizeof(void*)*2 + 8, x_15);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 16, x_4);
x_23 = lean_box(0);
x_24 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(x_11, x_10, x_16, x_12, x_22, x_23, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec_ref(x_12);
return x_24;
}
}
block_42:
{
lean_object* x_33; 
lean_inc(x_7);
lean_inc_ref(x_6);
x_33 = lean_apply_4(x_2, x_32, x_6, x_7, x_28);
if (lean_obj_tag(x_33) == 0)
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_11 = x_26;
x_12 = x_27;
x_13 = x_29;
x_14 = x_30;
x_15 = x_31;
x_16 = x_34;
x_17 = x_35;
goto block_25;
}
else
{
uint8_t x_36; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_ctor_set_tag(x_33, 1);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec_ref(x_33);
x_41 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__2;
x_11 = x_26;
x_12 = x_27;
x_13 = x_29;
x_14 = x_30;
x_15 = x_31;
x_16 = x_41;
x_17 = x_40;
goto block_25;
}
}
block_57:
{
if (x_46 == 0)
{
double x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__0;
x_51 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_5);
lean_ctor_set_float(x_51, sizeof(void*)*2, x_50);
lean_ctor_set_float(x_51, sizeof(void*)*2 + 8, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 16, x_4);
x_52 = lean_box(0);
x_53 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(x_43, x_10, x_48, x_44, x_51, x_52, x_6, x_7, x_49);
lean_dec(x_7);
lean_dec_ref(x_44);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_5);
lean_ctor_set_float(x_54, sizeof(void*)*2, x_45);
lean_ctor_set_float(x_54, sizeof(void*)*2 + 8, x_47);
lean_ctor_set_uint8(x_54, sizeof(void*)*2 + 16, x_4);
x_55 = lean_box(0);
x_56 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(x_43, x_10, x_48, x_44, x_54, x_55, x_6, x_7, x_49);
lean_dec(x_7);
lean_dec_ref(x_44);
return x_56;
}
}
block_74:
{
lean_object* x_65; 
lean_inc(x_7);
lean_inc_ref(x_6);
x_65 = lean_apply_4(x_2, x_63, x_6, x_7, x_62);
if (lean_obj_tag(x_65) == 0)
{
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_43 = x_58;
x_44 = x_59;
x_45 = x_61;
x_46 = x_60;
x_47 = x_64;
x_48 = x_66;
x_49 = x_67;
goto block_57;
}
else
{
uint8_t x_68; 
lean_dec_ref(x_59);
lean_dec_ref(x_58);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_ctor_set_tag(x_65, 1);
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_dec_ref(x_65);
x_73 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__2;
x_43 = x_58;
x_44 = x_59;
x_45 = x_61;
x_46 = x_60;
x_47 = x_64;
x_48 = x_73;
x_49 = x_72;
goto block_57;
}
}
block_124:
{
uint8_t x_87; 
x_87 = lean_unbox(x_76);
lean_dec(x_76);
if (x_87 == 0)
{
if (x_86 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_88 = lean_st_ref_take(x_7, x_80);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 4);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec_ref(x_88);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_89, 4);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_90, 0);
x_96 = l_Lean_PersistentArray_append___redArg(x_82, x_95);
lean_dec_ref(x_95);
lean_ctor_set(x_90, 0, x_96);
x_97 = lean_st_ref_set(x_7, x_89, x_91);
lean_dec(x_7);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_85, x_98);
lean_dec_ref(x_85);
return x_99;
}
else
{
uint64_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get_uint64(x_90, sizeof(void*)*1);
x_101 = lean_ctor_get(x_90, 0);
lean_inc(x_101);
lean_dec(x_90);
x_102 = l_Lean_PersistentArray_append___redArg(x_82, x_101);
lean_dec_ref(x_101);
x_103 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set_uint64(x_103, sizeof(void*)*1, x_100);
lean_ctor_set(x_89, 4, x_103);
x_104 = lean_st_ref_set(x_7, x_89, x_91);
lean_dec(x_7);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_85, x_105);
lean_dec_ref(x_85);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_107 = lean_ctor_get(x_89, 0);
x_108 = lean_ctor_get(x_89, 1);
x_109 = lean_ctor_get(x_89, 2);
x_110 = lean_ctor_get(x_89, 3);
x_111 = lean_ctor_get(x_89, 5);
x_112 = lean_ctor_get(x_89, 6);
x_113 = lean_ctor_get(x_89, 7);
x_114 = lean_ctor_get(x_89, 8);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_89);
x_115 = lean_ctor_get_uint64(x_90, sizeof(void*)*1);
x_116 = lean_ctor_get(x_90, 0);
lean_inc_ref(x_116);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_117 = x_90;
} else {
 lean_dec_ref(x_90);
 x_117 = lean_box(0);
}
x_118 = l_Lean_PersistentArray_append___redArg(x_82, x_116);
lean_dec_ref(x_116);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 1, 8);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set_uint64(x_119, sizeof(void*)*1, x_115);
x_120 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_120, 0, x_107);
lean_ctor_set(x_120, 1, x_108);
lean_ctor_set(x_120, 2, x_109);
lean_ctor_set(x_120, 3, x_110);
lean_ctor_set(x_120, 4, x_119);
lean_ctor_set(x_120, 5, x_111);
lean_ctor_set(x_120, 6, x_112);
lean_ctor_set(x_120, 7, x_113);
lean_ctor_set(x_120, 8, x_114);
x_121 = lean_st_ref_set(x_7, x_120, x_91);
lean_dec(x_7);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_85, x_122);
lean_dec_ref(x_85);
return x_123;
}
}
else
{
lean_dec_ref(x_82);
x_26 = x_78;
x_27 = x_79;
x_28 = x_80;
x_29 = x_81;
x_30 = x_83;
x_31 = x_84;
x_32 = x_85;
goto block_42;
}
}
else
{
lean_dec_ref(x_82);
x_26 = x_78;
x_27 = x_79;
x_28 = x_80;
x_29 = x_81;
x_30 = x_83;
x_31 = x_84;
x_32 = x_85;
goto block_42;
}
}
block_136:
{
double x_134; uint8_t x_135; 
x_134 = lean_float_sub(x_131, x_130);
x_135 = lean_float_decLt(x_133, x_134);
x_78 = x_125;
x_79 = x_126;
x_80 = x_127;
x_81 = x_129;
x_82 = x_128;
x_83 = x_130;
x_84 = x_131;
x_85 = x_132;
x_86 = x_135;
goto block_124;
}
block_158:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; double x_146; double x_147; lean_object* x_148; uint8_t x_149; 
x_143 = lean_io_get_num_heartbeats(x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
x_146 = lean_float_of_nat(x_137);
x_147 = lean_float_of_nat(x_144);
x_148 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__3;
x_149 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_9, x_148);
if (x_149 == 0)
{
lean_dec(x_9);
lean_inc_ref(x_141);
x_78 = x_138;
x_79 = x_141;
x_80 = x_145;
x_81 = x_149;
x_82 = x_140;
x_83 = x_146;
x_84 = x_147;
x_85 = x_141;
x_86 = x_149;
goto block_124;
}
else
{
if (x_139 == 0)
{
lean_object* x_150; lean_object* x_151; double x_152; double x_153; double x_154; 
x_150 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__4;
x_151 = l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(x_9, x_150);
lean_dec(x_9);
x_152 = lean_float_of_nat(x_151);
x_153 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__5;
x_154 = lean_float_div(x_152, x_153);
lean_inc_ref(x_141);
x_125 = x_138;
x_126 = x_141;
x_127 = x_145;
x_128 = x_140;
x_129 = x_149;
x_130 = x_146;
x_131 = x_147;
x_132 = x_141;
x_133 = x_154;
goto block_136;
}
else
{
lean_object* x_155; lean_object* x_156; double x_157; 
x_155 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__4;
x_156 = l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(x_9, x_155);
lean_dec(x_9);
x_157 = lean_float_of_nat(x_156);
lean_inc_ref(x_141);
x_125 = x_138;
x_126 = x_141;
x_127 = x_145;
x_128 = x_140;
x_129 = x_149;
x_130 = x_146;
x_131 = x_147;
x_132 = x_141;
x_133 = x_157;
goto block_136;
}
}
}
block_205:
{
uint8_t x_168; 
x_168 = lean_unbox(x_76);
lean_dec(x_76);
if (x_168 == 0)
{
if (x_167 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_169 = lean_st_ref_take(x_7, x_164);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 4);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec_ref(x_169);
x_173 = !lean_is_exclusive(x_170);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_170, 4);
lean_dec(x_174);
x_175 = !lean_is_exclusive(x_171);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_171, 0);
x_177 = l_Lean_PersistentArray_append___redArg(x_163, x_176);
lean_dec_ref(x_176);
lean_ctor_set(x_171, 0, x_177);
x_178 = lean_st_ref_set(x_7, x_170, x_172);
lean_dec(x_7);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_165, x_179);
lean_dec_ref(x_165);
return x_180;
}
else
{
uint64_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get_uint64(x_171, sizeof(void*)*1);
x_182 = lean_ctor_get(x_171, 0);
lean_inc(x_182);
lean_dec(x_171);
x_183 = l_Lean_PersistentArray_append___redArg(x_163, x_182);
lean_dec_ref(x_182);
x_184 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set_uint64(x_184, sizeof(void*)*1, x_181);
lean_ctor_set(x_170, 4, x_184);
x_185 = lean_st_ref_set(x_7, x_170, x_172);
lean_dec(x_7);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_165, x_186);
lean_dec_ref(x_165);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint64_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_188 = lean_ctor_get(x_170, 0);
x_189 = lean_ctor_get(x_170, 1);
x_190 = lean_ctor_get(x_170, 2);
x_191 = lean_ctor_get(x_170, 3);
x_192 = lean_ctor_get(x_170, 5);
x_193 = lean_ctor_get(x_170, 6);
x_194 = lean_ctor_get(x_170, 7);
x_195 = lean_ctor_get(x_170, 8);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_170);
x_196 = lean_ctor_get_uint64(x_171, sizeof(void*)*1);
x_197 = lean_ctor_get(x_171, 0);
lean_inc_ref(x_197);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_198 = x_171;
} else {
 lean_dec_ref(x_171);
 x_198 = lean_box(0);
}
x_199 = l_Lean_PersistentArray_append___redArg(x_163, x_197);
lean_dec_ref(x_197);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 1, 8);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set_uint64(x_200, sizeof(void*)*1, x_196);
x_201 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_201, 0, x_188);
lean_ctor_set(x_201, 1, x_189);
lean_ctor_set(x_201, 2, x_190);
lean_ctor_set(x_201, 3, x_191);
lean_ctor_set(x_201, 4, x_200);
lean_ctor_set(x_201, 5, x_192);
lean_ctor_set(x_201, 6, x_193);
lean_ctor_set(x_201, 7, x_194);
lean_ctor_set(x_201, 8, x_195);
x_202 = lean_st_ref_set(x_7, x_201, x_172);
lean_dec(x_7);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_165, x_203);
lean_dec_ref(x_165);
return x_204;
}
}
else
{
lean_dec_ref(x_163);
x_58 = x_159;
x_59 = x_160;
x_60 = x_162;
x_61 = x_161;
x_62 = x_164;
x_63 = x_165;
x_64 = x_166;
goto block_74;
}
}
else
{
lean_dec_ref(x_163);
x_58 = x_159;
x_59 = x_160;
x_60 = x_162;
x_61 = x_161;
x_62 = x_164;
x_63 = x_165;
x_64 = x_166;
goto block_74;
}
}
block_217:
{
double x_215; uint8_t x_216; 
x_215 = lean_float_sub(x_213, x_209);
x_216 = lean_float_decLt(x_214, x_215);
x_159 = x_206;
x_160 = x_207;
x_161 = x_209;
x_162 = x_208;
x_163 = x_210;
x_164 = x_211;
x_165 = x_212;
x_166 = x_213;
x_167 = x_216;
goto block_205;
}
block_242:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; double x_227; double x_228; double x_229; double x_230; double x_231; lean_object* x_232; uint8_t x_233; 
x_224 = lean_io_mono_nanos_now(x_223);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec_ref(x_224);
x_227 = lean_float_of_nat(x_218);
x_228 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__6;
x_229 = lean_float_div(x_227, x_228);
x_230 = lean_float_of_nat(x_225);
x_231 = lean_float_div(x_230, x_228);
x_232 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__3;
x_233 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_9, x_232);
if (x_233 == 0)
{
lean_dec(x_9);
lean_inc_ref(x_222);
x_159 = x_219;
x_160 = x_222;
x_161 = x_229;
x_162 = x_233;
x_163 = x_221;
x_164 = x_226;
x_165 = x_222;
x_166 = x_231;
x_167 = x_233;
goto block_205;
}
else
{
if (x_220 == 0)
{
lean_object* x_234; lean_object* x_235; double x_236; double x_237; double x_238; 
x_234 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__4;
x_235 = l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(x_9, x_234);
lean_dec(x_9);
x_236 = lean_float_of_nat(x_235);
x_237 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__5;
x_238 = lean_float_div(x_236, x_237);
lean_inc_ref(x_222);
x_206 = x_219;
x_207 = x_222;
x_208 = x_233;
x_209 = x_229;
x_210 = x_221;
x_211 = x_226;
x_212 = x_222;
x_213 = x_231;
x_214 = x_238;
goto block_217;
}
else
{
lean_object* x_239; lean_object* x_240; double x_241; 
x_239 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__4;
x_240 = l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(x_9, x_239);
lean_dec(x_9);
x_241 = lean_float_of_nat(x_240);
lean_inc_ref(x_222);
x_206 = x_219;
x_207 = x_222;
x_208 = x_233;
x_209 = x_229;
x_210 = x_221;
x_211 = x_226;
x_212 = x_222;
x_213 = x_231;
x_214 = x_241;
goto block_217;
}
}
}
block_268:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_243 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_7, x_77);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec_ref(x_243);
x_246 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__7;
x_247 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_9, x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_io_mono_nanos_now(x_245);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec_ref(x_248);
lean_inc(x_7);
lean_inc_ref(x_6);
x_251 = lean_apply_3(x_3, x_6, x_7, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec_ref(x_251);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_252);
lean_inc(x_244);
x_218 = x_249;
x_219 = x_244;
x_220 = x_247;
x_221 = x_244;
x_222 = x_254;
x_223 = x_253;
goto block_242;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_251, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_251, 1);
lean_inc(x_256);
lean_dec_ref(x_251);
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_255);
lean_inc(x_244);
x_218 = x_249;
x_219 = x_244;
x_220 = x_247;
x_221 = x_244;
x_222 = x_257;
x_223 = x_256;
goto block_242;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_io_get_num_heartbeats(x_245);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec_ref(x_258);
lean_inc(x_7);
lean_inc_ref(x_6);
x_261 = lean_apply_3(x_3, x_6, x_7, x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec_ref(x_261);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_262);
lean_inc(x_244);
x_137 = x_259;
x_138 = x_244;
x_139 = x_247;
x_140 = x_244;
x_141 = x_264;
x_142 = x_263;
goto block_158;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_261, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_261, 1);
lean_inc(x_266);
lean_dec_ref(x_261);
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_265);
lean_inc(x_244);
x_137 = x_259;
x_138 = x_244;
x_139 = x_247;
x_140 = x_244;
x_141 = x_267;
x_142 = x_266;
goto block_158;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_4, 1);
x_11 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
x_14 = lean_string_dec_eq(x_10, x_13);
if (x_14 == 0)
{
return x_1;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__2;
x_16 = lean_string_dec_eq(x_9, x_15);
if (x_16 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__3;
x_18 = lean_string_dec_eq(x_9, x_17);
if (x_18 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; uint8_t x_140; uint8_t x_156; 
x_131 = 2;
x_156 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_186_(x_3, x_131);
if (x_156 == 0)
{
x_140 = x_156;
goto block_155;
}
else
{
uint8_t x_157; 
lean_inc_ref(x_2);
x_157 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_140 = x_157;
goto block_155;
}
block_78:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_st_ref_take(x_16, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_15, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 7);
lean_inc(x_23);
lean_dec_ref(x_15);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_20, 6);
lean_ctor_set(x_18, 1, x_23);
lean_ctor_set(x_18, 0, x_22);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_10);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_8);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_11);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_4);
x_28 = l_Lean_MessageLog_add(x_27, x_25);
lean_ctor_set(x_20, 6, x_28);
x_29 = lean_st_ref_set(x_16, x_20, x_21);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
x_38 = lean_ctor_get(x_20, 2);
x_39 = lean_ctor_get(x_20, 3);
x_40 = lean_ctor_get(x_20, 4);
x_41 = lean_ctor_get(x_20, 5);
x_42 = lean_ctor_get(x_20, 6);
x_43 = lean_ctor_get(x_20, 7);
x_44 = lean_ctor_get(x_20, 8);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
lean_ctor_set(x_18, 1, x_23);
lean_ctor_set(x_18, 0, x_22);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_10);
x_46 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_13);
lean_ctor_set(x_46, 2, x_14);
lean_ctor_set(x_46, 3, x_8);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_46, sizeof(void*)*5 + 1, x_11);
lean_ctor_set_uint8(x_46, sizeof(void*)*5 + 2, x_4);
x_47 = l_Lean_MessageLog_add(x_46, x_42);
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_37);
lean_ctor_set(x_48, 2, x_38);
lean_ctor_set(x_48, 3, x_39);
lean_ctor_set(x_48, 4, x_40);
lean_ctor_set(x_48, 5, x_41);
lean_ctor_set(x_48, 6, x_47);
lean_ctor_set(x_48, 7, x_43);
lean_ctor_set(x_48, 8, x_44);
x_49 = lean_st_ref_set(x_16, x_48, x_21);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_54 = lean_ctor_get(x_18, 0);
x_55 = lean_ctor_get(x_18, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_18);
x_56 = lean_ctor_get(x_15, 6);
lean_inc(x_56);
x_57 = lean_ctor_get(x_15, 7);
lean_inc(x_57);
lean_dec_ref(x_15);
x_58 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 2);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_54, 3);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_54, 4);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_54, 5);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_54, 6);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_54, 7);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_54, 8);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 lean_ctor_release(x_54, 6);
 lean_ctor_release(x_54, 7);
 lean_ctor_release(x_54, 8);
 x_67 = x_54;
} else {
 lean_dec_ref(x_54);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_56);
lean_ctor_set(x_68, 1, x_57);
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_10);
x_70 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_70, 0, x_12);
lean_ctor_set(x_70, 1, x_13);
lean_ctor_set(x_70, 2, x_14);
lean_ctor_set(x_70, 3, x_8);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_70, sizeof(void*)*5 + 1, x_11);
lean_ctor_set_uint8(x_70, sizeof(void*)*5 + 2, x_4);
x_71 = l_Lean_MessageLog_add(x_70, x_64);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 9, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_59);
lean_ctor_set(x_72, 2, x_60);
lean_ctor_set(x_72, 3, x_61);
lean_ctor_set(x_72, 4, x_62);
lean_ctor_set(x_72, 5, x_63);
lean_ctor_set(x_72, 6, x_71);
lean_ctor_set(x_72, 7, x_65);
lean_ctor_set(x_72, 8, x_66);
x_73 = lean_st_ref_set(x_16, x_72, x_55);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
block_107:
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_88 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_87, x_5, x_6, x_7);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_81);
x_92 = l_Lean_FileMap_toPosition(x_81, x_85);
lean_dec(x_85);
x_93 = l_Lean_FileMap_toPosition(x_81, x_86);
lean_dec(x_86);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
if (x_80 == 0)
{
lean_free_object(x_88);
lean_dec_ref(x_79);
x_8 = x_95;
x_9 = x_82;
x_10 = x_90;
x_11 = x_83;
x_12 = x_84;
x_13 = x_92;
x_14 = x_94;
x_15 = x_5;
x_16 = x_6;
x_17 = x_91;
goto block_78;
}
else
{
uint8_t x_96; 
lean_inc(x_90);
x_96 = l_Lean_MessageData_hasTag(x_79, x_90);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec_ref(x_94);
lean_dec_ref(x_92);
lean_dec(x_90);
lean_dec_ref(x_84);
lean_dec_ref(x_5);
x_97 = lean_box(0);
lean_ctor_set(x_88, 0, x_97);
return x_88;
}
else
{
lean_free_object(x_88);
x_8 = x_95;
x_9 = x_82;
x_10 = x_90;
x_11 = x_83;
x_12 = x_84;
x_13 = x_92;
x_14 = x_94;
x_15 = x_5;
x_16 = x_6;
x_17 = x_91;
goto block_78;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_88, 0);
x_99 = lean_ctor_get(x_88, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_88);
lean_inc_ref(x_81);
x_100 = l_Lean_FileMap_toPosition(x_81, x_85);
lean_dec(x_85);
x_101 = l_Lean_FileMap_toPosition(x_81, x_86);
lean_dec(x_86);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
if (x_80 == 0)
{
lean_dec_ref(x_79);
x_8 = x_103;
x_9 = x_82;
x_10 = x_98;
x_11 = x_83;
x_12 = x_84;
x_13 = x_100;
x_14 = x_102;
x_15 = x_5;
x_16 = x_6;
x_17 = x_99;
goto block_78;
}
else
{
uint8_t x_104; 
lean_inc(x_98);
x_104 = l_Lean_MessageData_hasTag(x_79, x_98);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_102);
lean_dec_ref(x_100);
lean_dec(x_98);
lean_dec_ref(x_84);
lean_dec_ref(x_5);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_99);
return x_106;
}
else
{
x_8 = x_103;
x_9 = x_82;
x_10 = x_98;
x_11 = x_83;
x_12 = x_84;
x_13 = x_100;
x_14 = x_102;
x_15 = x_5;
x_16 = x_6;
x_17 = x_99;
goto block_78;
}
}
}
}
block_118:
{
lean_object* x_116; 
x_116 = l_Lean_Syntax_getTailPos_x3f(x_113, x_111);
lean_dec(x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_inc(x_115);
x_79 = x_108;
x_80 = x_110;
x_81 = x_109;
x_82 = x_111;
x_83 = x_112;
x_84 = x_114;
x_85 = x_115;
x_86 = x_115;
goto block_107;
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_79 = x_108;
x_80 = x_110;
x_81 = x_109;
x_82 = x_111;
x_83 = x_112;
x_84 = x_114;
x_85 = x_115;
x_86 = x_117;
goto block_107;
}
}
block_130:
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Lean_replaceRef(x_1, x_124);
lean_dec(x_124);
x_127 = l_Lean_Syntax_getPos_x3f(x_126, x_122);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_unsigned_to_nat(0u);
x_108 = x_119;
x_109 = x_121;
x_110 = x_120;
x_111 = x_122;
x_112 = x_125;
x_113 = x_126;
x_114 = x_123;
x_115 = x_128;
goto block_118;
}
else
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec_ref(x_127);
x_108 = x_119;
x_109 = x_121;
x_110 = x_120;
x_111 = x_122;
x_112 = x_125;
x_113 = x_126;
x_114 = x_123;
x_115 = x_129;
goto block_118;
}
}
block_139:
{
if (x_138 == 0)
{
x_119 = x_135;
x_120 = x_133;
x_121 = x_132;
x_122 = x_137;
x_123 = x_134;
x_124 = x_136;
x_125 = x_3;
goto block_130;
}
else
{
x_119 = x_135;
x_120 = x_133;
x_121 = x_132;
x_122 = x_137;
x_123 = x_134;
x_124 = x_136;
x_125 = x_131;
goto block_130;
}
}
block_155:
{
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; 
x_141 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_142);
x_143 = lean_ctor_get(x_5, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_5, 5);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_146 = lean_box(x_140);
x_147 = lean_box(x_145);
x_148 = lean_alloc_closure((void*)(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0___boxed), 3, 2);
lean_closure_set(x_148, 0, x_146);
lean_closure_set(x_148, 1, x_147);
x_149 = 1;
x_150 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_186_(x_3, x_149);
if (x_150 == 0)
{
lean_dec(x_143);
x_132 = x_142;
x_133 = x_145;
x_134 = x_141;
x_135 = x_148;
x_136 = x_144;
x_137 = x_140;
x_138 = x_150;
goto block_139;
}
else
{
lean_object* x_151; uint8_t x_152; 
x_151 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___closed__0;
x_152 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_143, x_151);
lean_dec(x_143);
x_132 = x_142;
x_133 = x_145;
x_134 = x_141;
x_135 = x_148;
x_136 = x_144;
x_137 = x_140;
x_138 = x_152;
goto block_139;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_7);
return x_154;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 5);
lean_inc(x_7);
x_8 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = 2;
x_6 = 0;
x_7 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_get_set_stdout(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_get_set_stdout(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(x_7, x_9, x_13, x_12);
lean_dec_ref(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec_ref(x_10);
x_21 = lean_box(0);
x_22 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(x_7, x_9, x_21, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_get_set_stdin(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_get_set_stdin(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(x_7, x_9, x_13, x_12);
lean_dec_ref(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec_ref(x_10);
x_21 = lean_box(0);
x_22 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(x_7, x_9, x_21, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_get_set_stderr(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_get_set_stderr(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg___lam__0(x_7, x_9, x_13, x_12);
lean_dec_ref(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec_ref(x_10);
x_21 = lean_box(0);
x_22 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg___lam__0(x_7, x_9, x_21, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_ByteArray_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__3;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(131u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__0;
x_13 = lean_st_mk_ref(x_12, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_st_mk_ref(x_12, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_IO_FS_Stream_ofBuffer(x_14);
lean_inc(x_17);
x_20 = l_IO_FS_Stream_ofBuffer(x_17);
if (x_2 == 0)
{
x_21 = x_1;
goto block_38;
}
else
{
lean_object* x_39; 
lean_inc_ref(x_20);
x_39 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31), 6, 3);
lean_closure_set(x_39, 0, lean_box(0));
lean_closure_set(x_39, 1, x_20);
lean_closure_set(x_39, 2, x_1);
x_21 = x_39;
goto block_38;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
block_38:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28), 6, 3);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
x_23 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg(x_19, x_22, x_3, x_4, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = lean_string_validate_utf8(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_29);
x_31 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__4;
x_32 = l_panic___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30(x_31);
x_6 = x_28;
x_7 = x_24;
x_8 = x_32;
goto block_11;
}
else
{
lean_object* x_33; 
x_33 = lean_string_from_utf8_unchecked(x_29);
lean_dec_ref(x_29);
x_6 = x_28;
x_7 = x_24;
x_8 = x_33;
goto block_11;
}
}
else
{
uint8_t x_34; 
lean_dec(x_17);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0;
x_4 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4;
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2;
x_3 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_16; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_io_get_tid(x_6);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_st_ref_take(x_5, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_33 = lean_ctor_get(x_30, 6);
x_34 = lean_ctor_get(x_30, 8);
lean_dec(x_34);
x_35 = lean_ctor_get(x_30, 7);
lean_dec(x_35);
x_36 = lean_ctor_get(x_30, 4);
lean_dec(x_36);
x_37 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
x_38 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_unbox_uint64(x_27);
lean_dec(x_27);
lean_ctor_set_uint64(x_38, sizeof(void*)*1, x_39);
x_40 = l_Lean_MessageLog_markAllReported(x_33);
x_41 = 1;
x_42 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5;
x_43 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
lean_ctor_set(x_30, 8, x_43);
lean_ctor_set(x_30, 7, x_42);
lean_ctor_set(x_30, 6, x_40);
lean_ctor_set(x_30, 4, x_38);
x_44 = lean_st_ref_set(x_5, x_30, x_31);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_115_;
x_47 = lean_apply_1(x_1, x_2);
x_48 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
lean_inc(x_5);
lean_inc_ref(x_4);
x_49 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_46, x_3, x_47, x_41, x_48, x_4, x_5, x_45);
if (lean_obj_tag(x_49) == 0)
{
x_16 = x_49;
goto block_25;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = l_Lean_Exception_isInterrupt(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lean_Exception_toMessageData(x_50);
lean_inc_ref(x_4);
x_54 = l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25(x_53, x_4, x_5, x_51);
x_16 = x_54;
goto block_25;
}
else
{
lean_dec(x_50);
x_7 = x_51;
goto block_15;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_55 = lean_ctor_get(x_30, 0);
x_56 = lean_ctor_get(x_30, 1);
x_57 = lean_ctor_get(x_30, 2);
x_58 = lean_ctor_get(x_30, 3);
x_59 = lean_ctor_get(x_30, 5);
x_60 = lean_ctor_get(x_30, 6);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_30);
x_61 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
x_62 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_unbox_uint64(x_27);
lean_dec(x_27);
lean_ctor_set_uint64(x_62, sizeof(void*)*1, x_63);
x_64 = l_Lean_MessageLog_markAllReported(x_60);
x_65 = 1;
x_66 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5;
x_67 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
x_68 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_68, 0, x_55);
lean_ctor_set(x_68, 1, x_56);
lean_ctor_set(x_68, 2, x_57);
lean_ctor_set(x_68, 3, x_58);
lean_ctor_set(x_68, 4, x_62);
lean_ctor_set(x_68, 5, x_59);
lean_ctor_set(x_68, 6, x_64);
lean_ctor_set(x_68, 7, x_66);
lean_ctor_set(x_68, 8, x_67);
x_69 = lean_st_ref_set(x_5, x_68, x_31);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_115_;
x_72 = lean_apply_1(x_1, x_2);
x_73 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
lean_inc(x_5);
lean_inc_ref(x_4);
x_74 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_71, x_3, x_72, x_65, x_73, x_4, x_5, x_70);
if (lean_obj_tag(x_74) == 0)
{
x_16 = x_74;
goto block_25;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = l_Lean_Exception_isInterrupt(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = l_Lean_Exception_toMessageData(x_75);
lean_inc_ref(x_4);
x_79 = l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25(x_78, x_4, x_5, x_76);
x_16 = x_79;
goto block_25;
}
else
{
lean_dec(x_75);
x_7 = x_76;
goto block_15;
}
}
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(x_4, x_5, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_st_ref_get(x_5, x_9);
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
block_25:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_7 = x_17;
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(x_4, x_5, x_19);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_stderrAsMessages;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1), 6, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_2);
x_9 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___closed__0;
x_10 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_7, x_9);
lean_dec(x_7);
x_11 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(x_8, x_10, x_4, x_5, x_6);
return x_11;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0;
x_4 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__3;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__6() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__8() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0;
x_4 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__7;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__9() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__8;
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__6;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__10() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__9;
x_3 = lean_box(0);
x_4 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__5;
x_5 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0;
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Core_mkSnapshot(x_9, x_2, x_10, x_3, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__11;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__11;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed), 5, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2), 6, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_inc_ref(x_4);
x_9 = l_Lean_Core_wrapAsync___redArg(x_8, x_2, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3), 5, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_3);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3), 5, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(x_1, x_2, x_13, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(x_1, x_9, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_4);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9(x_1, x_2, x_3, x_12, x_5, x_13, x_14, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(x_1, x_2, x_12, x_4, x_5, x_13, x_14, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(x_1, x_9, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_4);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12(x_1, x_2, x_3, x_12, x_5, x_13, x_14, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12(x_1, x_2, x_12, x_4, x_5, x_13, x_14, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0(x_1, x_5, x_6, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_3);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(x_1, x_2, x_11, x_4, x_12, x_13, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
x_11 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__31___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsyncAsSnapshot(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_27; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
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
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_19 = lean_ctor_get(x_4, 11);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_21 = lean_ctor_get(x_4, 12);
lean_inc_ref(x_21);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 lean_ctor_release(x_4, 10);
 lean_ctor_release(x_4, 11);
 lean_ctor_release(x_4, 12);
 x_22 = x_4;
} else {
 lean_dec_ref(x_4);
 x_22 = lean_box(0);
}
x_27 = lean_nat_dec_le(x_1, x_11);
if (x_27 == 0)
{
lean_dec(x_11);
x_23 = x_1;
goto block_26;
}
else
{
lean_dec(x_1);
x_23 = x_11;
goto block_26;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 13, 2);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_8);
lean_ctor_set(x_24, 2, x_9);
lean_ctor_set(x_24, 3, x_10);
lean_ctor_set(x_24, 4, x_23);
lean_ctor_set(x_24, 5, x_12);
lean_ctor_set(x_24, 6, x_13);
lean_ctor_set(x_24, 7, x_14);
lean_ctor_set(x_24, 8, x_15);
lean_ctor_set(x_24, 9, x_16);
lean_ctor_set(x_24, 10, x_17);
lean_ctor_set(x_24, 11, x_19);
lean_ctor_set(x_24, 12, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*13, x_18);
lean_ctor_set_uint8(x_24, sizeof(void*)*13 + 1, x_20);
x_25 = lean_apply_3(x_3, x_24, x_5, x_6);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_withAtLeastMaxRecDepth___redArg___lam__0), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_3(x_1, lean_box(0), x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_withAtLeastMaxRecDepth___redArg___lam__0), 6, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_3(x_3, lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_nat_dec_eq(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_3);
x_8 = lean_apply_2(x_1, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_apply_1(x_3, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_catchInternalId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_3(x_6, lean_box(0), x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_catchInternalId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_apply_3(x_9, lean_box(0), x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_catchInternalId___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_catchInternalId(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = l_List_elem___redArg(x_2, x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_4);
x_9 = lean_apply_2(x_1, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_4, x_5);
return x_10;
}
}
}
}
static lean_object* _init_l_Lean_catchInternalIds___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_29____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = l_Lean_catchInternalIds___redArg___closed__0;
x_8 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___redArg___lam__0), 5, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_apply_3(x_6, lean_box(0), x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_4);
x_10 = l_Lean_catchInternalIds___redArg___closed__0;
x_11 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___redArg___lam__0), 5, 4);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_7);
x_12 = lean_apply_3(x_9, lean_box(0), x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_catchInternalIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__0;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_81_;
x_11 = lean_string_dec_eq(x_6, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_isMaxHeartbeat(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkArrow___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_mkArrow___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkArrow___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_mkArrow___redArg___closed__1;
x_6 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_5, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = 0;
x_10 = l_Lean_Expr_forallE___override(x_8, x_1, x_2, x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = 0;
x_14 = l_Lean_Expr_forallE___override(x_11, x_1, x_2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkArrow___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkArrow___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkArrow(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = 1;
x_9 = lean_usize_sub(x_2, x_8);
x_10 = lean_array_uget(x_1, x_9);
x_11 = l_Lean_mkArrow___redArg(x_10, x_4, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_2 = x_9;
x_4 = x_12;
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrowN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = 0;
x_12 = l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(x_1, x_10, x_11, x_2, x_4, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrowN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkArrowN(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Empty", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrec", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recOn", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesOn", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_12; uint8_t x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
x_14 = lean_is_aux_recursor(x_2, x_4);
if (x_14 == 0)
{
x_12 = x_14;
goto block_13;
}
else
{
uint8_t x_15; 
lean_inc(x_4);
lean_inc_ref(x_2);
x_15 = l_Lean_isCasesOnRecursor(x_2, x_4);
if (x_15 == 0)
{
x_12 = x_14;
goto block_13;
}
else
{
goto block_11;
}
}
block_9:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_6 = l_Array_contains___redArg(x_1, x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
block_11:
{
uint8_t x_10; 
lean_inc(x_4);
x_10 = l_Lean_isRecCore(x_2, x_4);
if (x_10 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_10;
}
else
{
goto block_9;
}
}
block_13:
{
if (x_12 == 0)
{
goto block_11;
}
else
{
lean_dec_ref(x_2);
goto block_9;
}
}
}
else
{
uint8_t x_16; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = 0;
return x_16;
}
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_10; 
x_10 = lean_find_expr(x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
goto block_9;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1;
x_14 = l_Lean_MessageData_ofName(x_12);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___redArg(x_3, x_4, x_17);
return x_18;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_inc_ref(x_3);
x_8 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed), 6, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_box(0);
x_10 = l_Lean_Declaration_foldExprM___redArg(x_3, x_5, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_5);
x_9 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2), 6, 5);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_2(x_3, x_5, x_6);
x_9 = l_Lean_profileitIOUnsafe___redArg(x_1, x_2, x_8, x_4, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_wait(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lean_traceBlock___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("blocked", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_traceBlock___redArg___lam__2___closed__0;
x_7 = lean_box(0);
x_8 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_6, x_5, x_1, x_7, x_2, x_3, x_4);
lean_dec(x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_traceBlock___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("block", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_traceBlock___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_traceBlock___redArg___closed__0;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_io_get_task_state(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 2)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = lean_task_get_own(x_2);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_task_get_own(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec_ref(x_6);
lean_inc_ref(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__0___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_17, 0, x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__2), 4, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_traceBlock___redArg___closed__1;
x_20 = 1;
x_21 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_19, x_16, x_18, x_20, x_1, x_3, x_4, x_15);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_traceBlock___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_profileitM___at___Lean_traceBlock_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_traceBlock___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_traceBlock___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDeclsImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_lcnf_compile_decls(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 5);
lean_dec(x_11);
x_12 = l_Lean_Environment_setExporting(x_10, x_2);
lean_ctor_set(x_7, 5, x_3);
lean_ctor_set(x_7, 0, x_12);
x_13 = lean_st_ref_set(x_1, x_7, x_8);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 6);
x_26 = lean_ctor_get(x_7, 7);
x_27 = lean_ctor_get(x_7, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_28 = l_Lean_Environment_setExporting(x_20, x_2);
x_29 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_3);
lean_ctor_set(x_29, 6, x_25);
lean_ctor_set(x_29, 7, x_26);
lean_ctor_set(x_29, 8, x_27);
x_30 = lean_st_ref_set(x_1, x_29, x_8);
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
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_2 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_4, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 5);
lean_dec(x_17);
x_18 = 0;
x_19 = l_Lean_Environment_setExporting(x_16, x_18);
x_20 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_13, 5, x_20);
lean_ctor_set(x_13, 0, x_19);
x_21 = lean_st_ref_set(x_4, x_13, x_14);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_4);
x_23 = lean_apply_3(x_1, x_3, x_4, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___lam__0(x_4, x_11, x_20, x_26, x_25);
lean_dec_ref(x_26);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec_ref(x_23);
x_34 = lean_box(0);
x_35 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___lam__0(x_4, x_11, x_20, x_34, x_33);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_32);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_ctor_get(x_13, 1);
x_42 = lean_ctor_get(x_13, 2);
x_43 = lean_ctor_get(x_13, 3);
x_44 = lean_ctor_get(x_13, 4);
x_45 = lean_ctor_get(x_13, 6);
x_46 = lean_ctor_get(x_13, 7);
x_47 = lean_ctor_get(x_13, 8);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_13);
x_48 = 0;
x_49 = l_Lean_Environment_setExporting(x_40, x_48);
x_50 = l_Lean_Core_instInhabitedCache___closed__2;
x_51 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_41);
lean_ctor_set(x_51, 2, x_42);
lean_ctor_set(x_51, 3, x_43);
lean_ctor_set(x_51, 4, x_44);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set(x_51, 6, x_45);
lean_ctor_set(x_51, 7, x_46);
lean_ctor_set(x_51, 8, x_47);
x_52 = lean_st_ref_set(x_4, x_51, x_14);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_4);
x_54 = lean_apply_3(x_1, x_3, x_4, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
lean_inc(x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_55);
x_58 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___lam__0(x_4, x_11, x_50, x_57, x_56);
lean_dec_ref(x_57);
lean_dec(x_4);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_dec_ref(x_54);
x_64 = lean_box(0);
x_65 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___lam__0(x_4, x_11, x_50, x_64, x_63);
lean_dec(x_4);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_name_eq(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_4);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
lean_dec_ref(x_6);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___redArg(x_2, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2___redArg(x_5, x_2);
return x_22;
}
else
{
lean_dec_ref(x_5);
return x_21;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_23);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Name_hash___override(x_2);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_24, x_37);
lean_dec_ref(x_24);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___redArg(x_2, x_38);
lean_dec(x_38);
return x_39;
}
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_compileDecls_doCompile_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_6 = 1;
x_7 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_8 = l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1___redArg(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec_ref(x_1);
return x_6;
}
else
{
if (x_5 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_6;
}
}
}
else
{
uint8_t x_12; 
lean_dec_ref(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Core_saveState___redArg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_4);
x_9 = lean_lcnf_compile_decls(x_1, x_3, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_Core_SavedState_restore___redArg(x_7, x_4, x_11);
lean_dec(x_4);
lean_dec(x_7);
if (x_2 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_box(x_2);
lean_inc_ref(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__0___boxed), 5, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_13);
lean_free_object(x_6);
lean_dec(x_8);
lean_dec_ref(x_1);
x_15 = 1;
x_16 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(x_11, x_15, x_3, x_4, x_9);
return x_16;
}
else
{
if (x_14 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_free_object(x_6);
lean_dec(x_8);
lean_dec_ref(x_1);
x_17 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(x_11, x_14, x_3, x_4, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_18);
lean_dec(x_8);
x_19 = l_Lean_Environment_constants(x_18);
x_20 = 0;
x_21 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_22 = l_Array_anyMUnsafe_any___at___Lean_compileDecls_doCompile_spec__6(x_19, x_1, x_20, x_21);
lean_dec_ref(x_1);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_6);
x_23 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(x_11, x_14, x_3, x_4, x_9);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = lean_box(0);
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = lean_box(x_2);
lean_inc_ref(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__0___boxed), 5, 2);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_1);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec_ref(x_1);
x_32 = 1;
x_33 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(x_28, x_32, x_3, x_4, x_26);
return x_33;
}
else
{
if (x_31 == 0)
{
lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec_ref(x_1);
x_34 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(x_28, x_31, x_3, x_4, x_26);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_35);
lean_dec(x_25);
x_36 = l_Lean_Environment_constants(x_35);
x_37 = 0;
x_38 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_39 = l_Array_anyMUnsafe_any___at___Lean_compileDecls_doCompile_spec__6(x_36, x_1, x_37, x_38);
lean_dec_ref(x_1);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(x_28, x_31, x_3, x_4, x_26);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_26);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___lam__0(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___redArg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__0(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2_spec__2(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_SMap_contains___at___Lean_compileDecls_doCompile_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_compileDecls_doCompile_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_compileDecls_doCompile_spec__6(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_compileDecls_doCompile___lam__0(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_compileDecls_doCompile(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 5);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_5, 5, x_10);
lean_ctor_set(x_5, 0, x_1);
x_11 = lean_st_ref_set(x_2, x_5, x_6);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 6);
x_23 = lean_ctor_get(x_5, 7);
x_24 = lean_ctor_get(x_5, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_25 = l_Lean_Core_instInhabitedCache___closed__2;
x_26 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_22);
lean_ctor_set(x_26, 7, x_23);
lean_ctor_set(x_26, 8, x_24);
x_27 = lean_st_ref_set(x_2, x_26, x_6);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___Lean_compileDecls_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = l_Lean_Environment_PromiseCheckedResult_commitChecked(x_2, x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_setEnv___at___Lean_compileDecls_spec__0___redArg(x_1, x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_7);
x_11 = l_Lean_compileDecls_doCompile(x_3, x_4, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = l_Lean_compileDecls___lam__0(x_7, x_2, x_14, x_13);
lean_dec_ref(x_14);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec_ref(x_11);
x_22 = lean_box(0);
x_23 = l_Lean_compileDecls___lam__0(x_7, x_2, x_22, x_21);
lean_dec(x_7);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_compileDecls___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler env", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_compileDecls___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_async;
return x_1;
}
}
static lean_object* _init_l_Lean_compileDecls___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compileDecls", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_compileDecls___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_compileDecls___closed__2;
x_2 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_29 = lean_ctor_get(x_3, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_31);
lean_dec(x_7);
x_32 = l_Lean_compileDecls___closed__1;
x_33 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_29, x_32);
lean_dec(x_29);
if (x_33 == 0)
{
lean_dec_ref(x_31);
lean_dec(x_30);
goto block_28;
}
else
{
uint8_t x_34; 
x_34 = l_Lean_Environment_isRealizing(x_31);
lean_dec_ref(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_35 = lean_st_ref_get(x_4, x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_38);
lean_dec(x_36);
lean_inc_ref(x_38);
x_39 = l_Lean_Environment_promiseChecked(x_38, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_43);
x_44 = l_Lean_setEnv___at___Lean_compileDecls_spec__0___redArg(x_42, x_4, x_41);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_IO_CancelToken_new(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_box(x_2);
x_50 = lean_alloc_closure((void*)(l_Lean_compileDecls___lam__1___boxed), 8, 4);
lean_closure_set(x_50, 0, x_43);
lean_closure_set(x_50, 1, x_40);
lean_closure_set(x_50, 2, x_1);
lean_closure_set(x_50, 3, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_47);
x_52 = l_Lean_compileDecls___closed__3;
x_53 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_52, x_33);
lean_inc_ref(x_51);
x_54 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_50, x_51, x_53, x_3, x_4, x_48);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_ctor_get(x_38, 2);
lean_inc_ref(x_57);
lean_dec_ref(x_38);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_io_map_task(x_55, x_57, x_58, x_34, x_56);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_68; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_68 = l_Lean_Syntax_getTailPos_x3f(x_30, x_34);
lean_dec(x_30);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
lean_free_object(x_59);
x_69 = lean_box(0);
x_63 = x_69;
goto block_67;
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_ctor_set(x_59, 1, x_71);
lean_ctor_set(x_59, 0, x_71);
lean_ctor_set(x_68, 0, x_59);
x_63 = x_68;
goto block_67;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
lean_dec(x_68);
lean_inc(x_72);
lean_ctor_set(x_59, 1, x_72);
lean_ctor_set(x_59, 0, x_72);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_59);
x_63 = x_73;
goto block_67;
}
}
block_67:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_51);
lean_ctor_set(x_65, 3, x_61);
x_66 = l_Lean_Core_logSnapshotTask___redArg(x_65, x_4, x_62);
lean_dec(x_4);
return x_66;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_81; 
x_74 = lean_ctor_get(x_59, 0);
x_75 = lean_ctor_get(x_59, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_59);
x_81 = l_Lean_Syntax_getTailPos_x3f(x_30, x_34);
lean_dec(x_30);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_76 = x_82;
goto block_80;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
lean_inc(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_83);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
x_76 = x_86;
goto block_80;
}
block_80:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_51);
lean_ctor_set(x_78, 3, x_74);
x_79 = l_Lean_Core_logSnapshotTask___redArg(x_78, x_4, x_75);
lean_dec(x_4);
return x_79;
}
}
}
else
{
lean_dec(x_30);
goto block_28;
}
}
block_28:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_compileDecls___closed__0;
lean_inc(x_4);
lean_inc_ref(x_3);
x_15 = l_Lean_traceBlock___redArg(x_14, x_13, x_3, x_4, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_compileDecls_doCompile(x_1, x_2, x_3, x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
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
return x_17;
}
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_setEnv___at___Lean_compileDecls_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___Lean_compileDecls_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_compileDecls___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_compileDecls___lam__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_compileDecls(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Compiler_getDeclNamesForCodeGen(x_1);
x_7 = l_Lean_compileDecls(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_compileDecl(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_getDiag(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_3 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getDiag___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getDiag(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*13);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isDiagnosticsEnabled___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_isDiagnosticsEnabled___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isDiagnosticsEnabled(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ImportM_runCoreM___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_ImportM_runCoreM___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__4() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0;
x_4 = l_Lean_ImportM_runCoreM___redArg___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_ImportM_runCoreM___redArg___closed__6;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instInhabitedCache___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instInhabitedCache___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4;
x_2 = l_Lean_ImportM_runCoreM___redArg___closed__9;
x_3 = l_Lean_ImportM_runCoreM___redArg___closed__8;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<ImportM>", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ImportM_runCoreM___redArg___closed__12;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_ImportM_runCoreM___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; uint8_t x_152; uint8_t x_175; 
x_4 = lean_io_get_num_heartbeats(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_ImportM_runCoreM___redArg___closed__2;
x_14 = l_Lean_ImportM_runCoreM___redArg___closed__3;
x_15 = l_Lean_ImportM_runCoreM___redArg___closed__4;
x_16 = l_Lean_Core_instInhabitedCache___closed__2;
x_17 = l_Lean_ImportM_runCoreM___redArg___closed__7;
x_18 = l_Lean_ImportM_runCoreM___redArg___closed__10;
x_19 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
lean_inc_ref(x_7);
x_20 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_16);
lean_ctor_set(x_20, 6, x_17);
lean_ctor_set(x_20, 7, x_18);
lean_ctor_set(x_20, 8, x_19);
x_21 = lean_st_mk_ref(x_20, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_122 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_123 = lean_st_ref_get(x_122, x_23);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_126 = lean_st_ref_get(x_22, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_129);
lean_dec(x_127);
x_130 = l_Lean_ImportM_runCoreM___redArg___closed__11;
x_131 = l_Lean_ImportM_runCoreM___redArg___closed__13;
x_132 = lean_box(0);
x_133 = lean_box(0);
x_134 = lean_box(0);
x_135 = l_Lean_ImportM_runCoreM___redArg___closed__14;
x_136 = 0;
x_137 = lean_box(0);
x_138 = l_Lean_useDiagnosticMsg___lam__2___closed__0;
x_139 = l_Lean_ImportM_runCoreM___redArg___closed__15;
x_175 = l_Lean_Kernel_isDiagnosticsEnabled(x_129);
lean_dec_ref(x_129);
if (x_175 == 0)
{
if (x_139 == 0)
{
lean_inc(x_22);
x_140 = x_22;
x_141 = x_128;
goto block_151;
}
else
{
x_152 = x_175;
goto block_174;
}
}
else
{
x_152 = x_139;
goto block_174;
}
block_75:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lean_Option_get___at___Lean_Core_getMaxHeartbeats_spec__0(x_8, x_24);
lean_dec_ref(x_24);
lean_inc(x_8);
x_41 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_41, 2, x_8);
lean_ctor_set(x_41, 3, x_28);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_29);
lean_ctor_set(x_41, 6, x_30);
lean_ctor_set(x_41, 7, x_31);
lean_ctor_set(x_41, 8, x_32);
lean_ctor_set(x_41, 9, x_33);
lean_ctor_set(x_41, 10, x_34);
lean_ctor_set(x_41, 11, x_35);
lean_ctor_set(x_41, 12, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*13, x_25);
lean_ctor_set_uint8(x_41, sizeof(void*)*13 + 1, x_36);
x_42 = lean_apply_3(x_1, x_41, x_38, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_st_ref_get(x_22, x_44);
lean_dec(x_22);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_22);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec_ref(x_42);
x_52 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_52);
lean_dec_ref(x_50);
x_53 = l_Lean_MessageData_toString(x_52, x_51);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_42, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
lean_dec_ref(x_50);
x_64 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_65 = l_Nat_reprFast(x_63);
x_66 = lean_string_append(x_64, x_65);
lean_dec_ref(x_65);
x_67 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_42, 0, x_67);
return x_42;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
lean_dec(x_42);
x_69 = lean_ctor_get(x_50, 0);
lean_inc(x_69);
lean_dec_ref(x_50);
x_70 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_71 = l_Nat_reprFast(x_69);
x_72 = lean_string_append(x_70, x_71);
lean_dec_ref(x_71);
x_73 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
}
}
}
block_93:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_78, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 7);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 8);
lean_inc(x_87);
x_88 = lean_ctor_get(x_78, 9);
lean_inc(x_88);
x_89 = lean_ctor_get(x_78, 10);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 11);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_78, sizeof(void*)*13 + 1);
x_92 = lean_ctor_get(x_78, 12);
lean_inc_ref(x_92);
lean_dec_ref(x_78);
x_24 = x_76;
x_25 = x_77;
x_26 = x_81;
x_27 = x_82;
x_28 = x_83;
x_29 = x_84;
x_30 = x_85;
x_31 = x_86;
x_32 = x_87;
x_33 = x_88;
x_34 = x_89;
x_35 = x_90;
x_36 = x_91;
x_37 = x_92;
x_38 = x_79;
x_39 = x_80;
goto block_75;
}
block_121:
{
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_st_ref_take(x_94, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
x_103 = !lean_is_exclusive(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_101, 0);
x_105 = lean_ctor_get(x_101, 5);
lean_dec(x_105);
x_106 = l_Lean_Kernel_enableDiag(x_104, x_96);
lean_ctor_set(x_101, 5, x_16);
lean_ctor_set(x_101, 0, x_106);
x_107 = lean_st_ref_set(x_94, x_101, x_102);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec_ref(x_107);
x_76 = x_95;
x_77 = x_96;
x_78 = x_97;
x_79 = x_94;
x_80 = x_108;
goto block_93;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_109 = lean_ctor_get(x_101, 0);
x_110 = lean_ctor_get(x_101, 1);
x_111 = lean_ctor_get(x_101, 2);
x_112 = lean_ctor_get(x_101, 3);
x_113 = lean_ctor_get(x_101, 4);
x_114 = lean_ctor_get(x_101, 6);
x_115 = lean_ctor_get(x_101, 7);
x_116 = lean_ctor_get(x_101, 8);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_101);
x_117 = l_Lean_Kernel_enableDiag(x_109, x_96);
x_118 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_111);
lean_ctor_set(x_118, 3, x_112);
lean_ctor_set(x_118, 4, x_113);
lean_ctor_set(x_118, 5, x_16);
lean_ctor_set(x_118, 6, x_114);
lean_ctor_set(x_118, 7, x_115);
lean_ctor_set(x_118, 8, x_116);
x_119 = lean_st_ref_set(x_94, x_118, x_102);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec_ref(x_119);
x_76 = x_95;
x_77 = x_96;
x_78 = x_97;
x_79 = x_94;
x_80 = x_120;
goto block_93;
}
}
else
{
x_76 = x_95;
x_77 = x_96;
x_78 = x_97;
x_79 = x_94;
x_80 = x_98;
goto block_93;
}
}
block_151:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; 
x_142 = lean_st_ref_get(x_140, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc_ref(x_145);
lean_dec(x_143);
x_146 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_147 = l_Lean_ImportM_runCoreM___redArg___closed__16;
lean_inc(x_124);
lean_inc(x_5);
x_148 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_148, 0, x_130);
lean_ctor_set(x_148, 1, x_131);
lean_ctor_set(x_148, 2, x_132);
lean_ctor_set(x_148, 3, x_9);
lean_ctor_set(x_148, 4, x_147);
lean_ctor_set(x_148, 5, x_133);
lean_ctor_set(x_148, 6, x_10);
lean_ctor_set(x_148, 7, x_134);
lean_ctor_set(x_148, 8, x_5);
lean_ctor_set(x_148, 9, x_135);
lean_ctor_set(x_148, 10, x_11);
lean_ctor_set(x_148, 11, x_137);
lean_ctor_set(x_148, 12, x_124);
lean_ctor_set_uint8(x_148, sizeof(void*)*13, x_139);
lean_ctor_set_uint8(x_148, sizeof(void*)*13 + 1, x_136);
x_149 = l_Lean_Option_get___at___Lean_useDiagnosticMsg_spec__0(x_8, x_138);
x_150 = l_Lean_Kernel_isDiagnosticsEnabled(x_145);
lean_dec_ref(x_145);
if (x_150 == 0)
{
if (x_149 == 0)
{
lean_dec_ref(x_148);
x_24 = x_146;
x_25 = x_149;
x_26 = x_130;
x_27 = x_131;
x_28 = x_9;
x_29 = x_133;
x_30 = x_10;
x_31 = x_134;
x_32 = x_5;
x_33 = x_135;
x_34 = x_11;
x_35 = x_137;
x_36 = x_136;
x_37 = x_124;
x_38 = x_140;
x_39 = x_144;
goto block_75;
}
else
{
lean_dec(x_124);
lean_dec(x_5);
x_94 = x_140;
x_95 = x_146;
x_96 = x_149;
x_97 = x_148;
x_98 = x_144;
x_99 = x_150;
goto block_121;
}
}
else
{
lean_dec(x_124);
lean_dec(x_5);
x_94 = x_140;
x_95 = x_146;
x_96 = x_149;
x_97 = x_148;
x_98 = x_144;
x_99 = x_149;
goto block_121;
}
}
block_174:
{
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_153 = lean_st_ref_take(x_22, x_128);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = !lean_is_exclusive(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_154, 0);
x_158 = lean_ctor_get(x_154, 5);
lean_dec(x_158);
x_159 = l_Lean_Kernel_enableDiag(x_157, x_139);
lean_ctor_set(x_154, 5, x_16);
lean_ctor_set(x_154, 0, x_159);
x_160 = lean_st_ref_set(x_22, x_154, x_155);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec_ref(x_160);
lean_inc(x_22);
x_140 = x_22;
x_141 = x_161;
goto block_151;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_162 = lean_ctor_get(x_154, 0);
x_163 = lean_ctor_get(x_154, 1);
x_164 = lean_ctor_get(x_154, 2);
x_165 = lean_ctor_get(x_154, 3);
x_166 = lean_ctor_get(x_154, 4);
x_167 = lean_ctor_get(x_154, 6);
x_168 = lean_ctor_get(x_154, 7);
x_169 = lean_ctor_get(x_154, 8);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_154);
x_170 = l_Lean_Kernel_enableDiag(x_162, x_139);
x_171 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
lean_ctor_set(x_171, 4, x_166);
lean_ctor_set(x_171, 5, x_16);
lean_ctor_set(x_171, 6, x_167);
lean_ctor_set(x_171, 7, x_168);
lean_ctor_set(x_171, 8, x_169);
x_172 = lean_st_ref_set(x_22, x_171, x_155);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec_ref(x_172);
lean_inc(x_22);
x_140 = x_22;
x_141 = x_173;
goto block_151;
}
}
else
{
lean_inc(x_22);
x_140 = x_22;
x_141 = x_128;
goto block_151;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ImportM_runCoreM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ImportM_runCoreM___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ImportM_runCoreM(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isRuntime(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Exception_isMaxHeartbeat(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Exception_isMaxRecDepth(x_1);
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isRuntime___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_isRuntime(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc_ref(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_12 = l_Lean_Exception_isInterrupt(x_7);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Exception_isRuntime(x_7);
x_9 = x_13;
goto block_11;
}
else
{
x_9 = x_12;
goto block_11;
}
block_11:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_6);
x_10 = lean_apply_4(x_2, x_7, x_3, x_4, x_8);
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_13 = l_Lean_Exception_isInterrupt(x_8);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Exception_isRuntime(x_8);
x_10 = x_14;
goto block_12;
}
else
{
x_10 = x_13;
goto block_12;
}
block_12:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_7);
x_11 = lean_apply_4(x_3, x_8, x_4, x_5, x_9);
return x_11;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc_ref(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l_Lean_Exception_isInterrupt(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_6);
x_10 = lean_apply_4(x_2, x_7, x_3, x_4, x_8);
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = l_Lean_Exception_isInterrupt(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_7);
x_11 = lean_apply_4(x_3, x_8, x_4, x_5, x_9);
return x_11;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instMonadExceptOfExceptionCoreM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_tryCatch), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instMonadExceptOfExceptionCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed), 5, 0);
x_2 = l_Lean_instMonadExceptOfExceptionCoreM___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_instMonadExceptOfExceptionCoreM___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instMonadRuntimeExceptionCoreM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_tryCatchRuntimeEx), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instMonadRuntimeExceptionCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instMonadRuntimeExceptionCoreM___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_apply_3(x_1, lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1), 5, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_apply_3(x_1, lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_3, lean_box(0), x_1);
x_8 = lean_apply_5(x_2, lean_box(0), x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_mapCoreM___redArg___lam__0), 6, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_3);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
x_10 = lean_apply_1(x_7, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_mapCoreM___redArg___lam__0), 6, 2);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_4);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
x_12 = lean_apply_1(x_9, lean_box(0));
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 6);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
lean_dec_ref(x_6);
x_11 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_free_object(x_4);
x_12 = lean_st_ref_take(x_2, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 6);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 6);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_14, 2);
x_20 = l_Lean_NameSet_insert(x_19, x_1);
lean_ctor_set(x_14, 2, x_20);
x_21 = lean_st_ref_set(x_2, x_13, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
x_32 = lean_ctor_get(x_14, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_33 = l_Lean_NameSet_insert(x_32, x_1);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_13, 6, x_34);
x_35 = lean_st_ref_set(x_2, x_13, x_15);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = 1;
x_39 = lean_box(x_38);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
x_43 = lean_ctor_get(x_13, 2);
x_44 = lean_ctor_get(x_13, 3);
x_45 = lean_ctor_get(x_13, 4);
x_46 = lean_ctor_get(x_13, 5);
x_47 = lean_ctor_get(x_13, 7);
x_48 = lean_ctor_get(x_13, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_49 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_14, 2);
lean_inc(x_51);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_52 = x_14;
} else {
 lean_dec_ref(x_14);
 x_52 = lean_box(0);
}
x_53 = l_Lean_NameSet_insert(x_51, x_1);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 3, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_42);
lean_ctor_set(x_55, 2, x_43);
lean_ctor_set(x_55, 3, x_44);
lean_ctor_set(x_55, 4, x_45);
lean_ctor_set(x_55, 5, x_46);
lean_ctor_set(x_55, 6, x_54);
lean_ctor_set(x_55, 7, x_47);
lean_ctor_set(x_55, 8, x_48);
x_56 = lean_st_ref_set(x_2, x_55, x_15);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = 1;
x_60 = lean_box(x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; lean_object* x_63; 
lean_dec(x_1);
x_62 = 0;
x_63 = lean_box(x_62);
lean_ctor_set(x_4, 0, x_63);
return x_4;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_4, 1);
lean_inc(x_64);
lean_dec(x_4);
x_65 = lean_ctor_get(x_6, 2);
lean_inc(x_65);
lean_dec_ref(x_6);
x_66 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_1, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_67 = lean_st_ref_take(x_2, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 6);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec_ref(x_67);
x_71 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 2);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_68, 3);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_68, 4);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_68, 5);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_68, 7);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_68, 8);
lean_inc_ref(x_78);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 lean_ctor_release(x_68, 5);
 lean_ctor_release(x_68, 6);
 lean_ctor_release(x_68, 7);
 lean_ctor_release(x_68, 8);
 x_79 = x_68;
} else {
 lean_dec_ref(x_68);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_69, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_69, 2);
lean_inc(x_82);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 x_83 = x_69;
} else {
 lean_dec_ref(x_69);
 x_83 = lean_box(0);
}
x_84 = l_Lean_NameSet_insert(x_82, x_1);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 3, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_84);
if (lean_is_scalar(x_79)) {
 x_86 = lean_alloc_ctor(0, 9, 0);
} else {
 x_86 = x_79;
}
lean_ctor_set(x_86, 0, x_71);
lean_ctor_set(x_86, 1, x_72);
lean_ctor_set(x_86, 2, x_73);
lean_ctor_set(x_86, 3, x_74);
lean_ctor_set(x_86, 4, x_75);
lean_ctor_set(x_86, 5, x_76);
lean_ctor_set(x_86, 6, x_85);
lean_ctor_set(x_86, 7, x_77);
lean_ctor_set(x_86, 8, x_78);
x_87 = lean_st_ref_set(x_2, x_86, x_70);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = 1;
x_91 = lean_box(x_90);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
else
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_64);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logMessageKind___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_logMessageKind___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logMessageKind(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l_Lean_Environment_enableRealizationsForConst(x_8, x_9, x_1, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_setEnv___at___Lean_compileDecls_spec__0___redArg(x_11, x_3, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_enableRealizationsForConst(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7148_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_927_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7148_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7148_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7148_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_;
x_2 = l___private_Lean_CoreM_0__Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7148_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7148_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7148_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7148_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17____x40_Lean_CoreM___hyg_927_;
x_2 = l___private_Lean_CoreM_0__Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7148_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7148_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7148u);
x_2 = l___private_Lean_CoreM_0__Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7148_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_initFn____x40_Lean_CoreM___hyg_7148_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_115_;
x_3 = 0;
x_4 = l___private_Lean_CoreM_0__Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7148_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_traceBlock___redArg___closed__1;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
return x_8;
}
else
{
return x_5;
}
}
}
lean_object* initialize_Lean_Util_RecDepth(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ResolveName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_InfoTree_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Language_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_RecDepth(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_6_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_6_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_6_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_6_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_6_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_6_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_6_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_6_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_6_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_6_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_6_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_6_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_6_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_6_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_41_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_41_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_41_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_41_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_41_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_41_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_41_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_41_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_41_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_41_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_41_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_41_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_41_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_41_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_41_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_41_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics_threshold);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_81_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_81_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_81_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_81_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_81_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_81_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_81_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_81_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_81_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_81_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_81_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_81_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_81_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_81_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_81_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_81_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_81_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_maxHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_maxHeartbeats);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_115_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_115_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_115_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_115_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_115_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_115_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_115_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_115_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_115_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_115_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_115_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_115_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_115_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_115_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_115_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_115_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_115_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_async = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_async);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_154_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_154_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_154_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_154_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_154_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_154_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_154_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_154_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_154_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_154_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_154_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_154_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_154_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_154_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_154_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_154_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_inServer = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_inServer);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_193_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_193_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_193_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_193_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_193_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_193_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_193_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_193_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_193_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_193_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_193_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_193_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_193_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_193_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_193_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_193_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_193_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_193_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_193_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_internal_cmdlineSnapshots = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_internal_cmdlineSnapshots);
lean_dec_ref(res);
}l_Lean_useDiagnosticMsg___lam__0___closed__0 = _init_l_Lean_useDiagnosticMsg___lam__0___closed__0();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__0___closed__0);
l_Lean_useDiagnosticMsg___lam__0___closed__1 = _init_l_Lean_useDiagnosticMsg___lam__0___closed__1();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__0___closed__1);
l_Lean_useDiagnosticMsg___lam__0___closed__2 = _init_l_Lean_useDiagnosticMsg___lam__0___closed__2();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__0___closed__2);
l_Lean_useDiagnosticMsg___lam__2___closed__0 = _init_l_Lean_useDiagnosticMsg___lam__2___closed__0();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__2___closed__0);
l_Lean_useDiagnosticMsg___lam__2___closed__1 = _init_l_Lean_useDiagnosticMsg___lam__2___closed__1();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__2___closed__1);
l_Lean_useDiagnosticMsg___lam__2___closed__2 = _init_l_Lean_useDiagnosticMsg___lam__2___closed__2();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__2___closed__2);
l_Lean_useDiagnosticMsg___lam__2___closed__3 = _init_l_Lean_useDiagnosticMsg___lam__2___closed__3();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__2___closed__3);
l_Lean_useDiagnosticMsg___lam__2___closed__4 = _init_l_Lean_useDiagnosticMsg___lam__2___closed__4();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__2___closed__4);
l_Lean_useDiagnosticMsg = _init_l_Lean_useDiagnosticMsg();
lean_mark_persistent(l_Lean_useDiagnosticMsg);
l_Lean_instInhabitedDeclNameGenerator___closed__0 = _init_l_Lean_instInhabitedDeclNameGenerator___closed__0();
lean_mark_persistent(l_Lean_instInhabitedDeclNameGenerator___closed__0);
l_Lean_instInhabitedDeclNameGenerator = _init_l_Lean_instInhabitedDeclNameGenerator();
lean_mark_persistent(l_Lean_instInhabitedDeclNameGenerator);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18____x40_Lean_CoreM___hyg_927_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19____x40_Lean_CoreM___hyg_927_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19____x40_Lean_CoreM___hyg_927_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19____x40_Lean_CoreM___hyg_927_);
if (builtin) {res = l___private_Lean_CoreM_0__Lean_Core_initFn____x40_Lean_CoreM___hyg_927_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Core_getMaxHeartbeats___closed__0 = _init_l_Lean_Core_getMaxHeartbeats___closed__0();
lean_mark_persistent(l_Lean_Core_getMaxHeartbeats___closed__0);
l_Lean_Core_instInhabitedCache___closed__0 = _init_l_Lean_Core_instInhabitedCache___closed__0();
lean_mark_persistent(l_Lean_Core_instInhabitedCache___closed__0);
l_Lean_Core_instInhabitedCache___closed__1 = _init_l_Lean_Core_instInhabitedCache___closed__1();
lean_mark_persistent(l_Lean_Core_instInhabitedCache___closed__1);
l_Lean_Core_instInhabitedCache___closed__2 = _init_l_Lean_Core_instInhabitedCache___closed__2();
lean_mark_persistent(l_Lean_Core_instInhabitedCache___closed__2);
l_Lean_Core_instInhabitedCache = _init_l_Lean_Core_instInhabitedCache();
lean_mark_persistent(l_Lean_Core_instInhabitedCache);
l_Lean_Core_instMonadCoreM___closed__0 = _init_l_Lean_Core_instMonadCoreM___closed__0();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__0);
l_Lean_Core_instMonadCoreM___closed__1 = _init_l_Lean_Core_instMonadCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__1);
l_Lean_Core_instMonadCoreM = _init_l_Lean_Core_instMonadCoreM();
lean_mark_persistent(l_Lean_Core_instMonadCoreM);
l_Lean_Core_instInhabitedCoreM___lam__0___closed__0 = _init_l_Lean_Core_instInhabitedCoreM___lam__0___closed__0();
lean_mark_persistent(l_Lean_Core_instInhabitedCoreM___lam__0___closed__0);
l_Lean_Core_instInhabitedCoreM___lam__0___closed__1 = _init_l_Lean_Core_instInhabitedCoreM___lam__0___closed__1();
lean_mark_persistent(l_Lean_Core_instInhabitedCoreM___lam__0___closed__1);
l_Lean_Core_instMonadRefCoreM = _init_l_Lean_Core_instMonadRefCoreM();
lean_mark_persistent(l_Lean_Core_instMonadRefCoreM);
l_Lean_Core_instMonadEnvCoreM = _init_l_Lean_Core_instMonadEnvCoreM();
lean_mark_persistent(l_Lean_Core_instMonadEnvCoreM);
l_Lean_Core_instMonadOptionsCoreM = _init_l_Lean_Core_instMonadOptionsCoreM();
lean_mark_persistent(l_Lean_Core_instMonadOptionsCoreM);
l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0 = _init_l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0();
lean_mark_persistent(l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0);
l_Lean_Core_instMonadWithOptionsCoreM = _init_l_Lean_Core_instMonadWithOptionsCoreM();
lean_mark_persistent(l_Lean_Core_instMonadWithOptionsCoreM);
l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0 = _init_l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0);
l_Lean_Core_instAddMessageContextCoreM___closed__0 = _init_l_Lean_Core_instAddMessageContextCoreM___closed__0();
lean_mark_persistent(l_Lean_Core_instAddMessageContextCoreM___closed__0);
l_Lean_Core_instAddMessageContextCoreM___closed__1 = _init_l_Lean_Core_instAddMessageContextCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instAddMessageContextCoreM___closed__1);
l_Lean_Core_instAddMessageContextCoreM___closed__2 = _init_l_Lean_Core_instAddMessageContextCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instAddMessageContextCoreM___closed__2);
l_Lean_Core_instAddMessageContextCoreM = _init_l_Lean_Core_instAddMessageContextCoreM();
lean_mark_persistent(l_Lean_Core_instAddMessageContextCoreM);
l_Lean_Core_instMonadNameGeneratorCoreM = _init_l_Lean_Core_instMonadNameGeneratorCoreM();
lean_mark_persistent(l_Lean_Core_instMonadNameGeneratorCoreM);
l_Lean_Core_instMonadDeclNameGeneratorCoreM = _init_l_Lean_Core_instMonadDeclNameGeneratorCoreM();
lean_mark_persistent(l_Lean_Core_instMonadDeclNameGeneratorCoreM);
l_Lean_Core_instMonadRecDepthCoreM = _init_l_Lean_Core_instMonadRecDepthCoreM();
lean_mark_persistent(l_Lean_Core_instMonadRecDepthCoreM);
l_Lean_Core_instMonadResolveNameCoreM = _init_l_Lean_Core_instMonadResolveNameCoreM();
lean_mark_persistent(l_Lean_Core_instMonadResolveNameCoreM);
l_Lean_Core_instMonadQuotationCoreM___closed__0 = _init_l_Lean_Core_instMonadQuotationCoreM___closed__0();
lean_mark_persistent(l_Lean_Core_instMonadQuotationCoreM___closed__0);
l_Lean_Core_instMonadQuotationCoreM = _init_l_Lean_Core_instMonadQuotationCoreM();
lean_mark_persistent(l_Lean_Core_instMonadQuotationCoreM);
l_Lean_Core_instMonadInfoTreeCoreM = _init_l_Lean_Core_instMonadInfoTreeCoreM();
lean_mark_persistent(l_Lean_Core_instMonadInfoTreeCoreM);
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__2);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__7 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__7();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__7);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__8 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__8();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__8);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__9 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__9();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__9);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__10 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__10();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__10);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__11 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__11();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__11);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__12 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__12();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__12);
l_Lean_Core_instantiateValueLevelParams___closed__0 = _init_l_Lean_Core_instantiateValueLevelParams___closed__0();
lean_mark_persistent(l_Lean_Core_instantiateValueLevelParams___closed__0);
l_Lean_Core_instantiateValueLevelParams___closed__1 = _init_l_Lean_Core_instantiateValueLevelParams___closed__1();
lean_mark_persistent(l_Lean_Core_instantiateValueLevelParams___closed__1);
l_Lean_Core_instantiateValueLevelParams___closed__2 = _init_l_Lean_Core_instantiateValueLevelParams___closed__2();
lean_mark_persistent(l_Lean_Core_instantiateValueLevelParams___closed__2);
l_Lean_Core_instMonadLiftIOCoreM___closed__0 = _init_l_Lean_Core_instMonadLiftIOCoreM___closed__0();
lean_mark_persistent(l_Lean_Core_instMonadLiftIOCoreM___closed__0);
l_Lean_Core_instMonadLiftIOCoreM = _init_l_Lean_Core_instMonadLiftIOCoreM();
lean_mark_persistent(l_Lean_Core_instMonadLiftIOCoreM);
l_Lean_Core_instMonadTraceCoreM = _init_l_Lean_Core_instMonadTraceCoreM();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM);
l_Lean_Core_CoreM_toIO___redArg___closed__0 = _init_l_Lean_Core_CoreM_toIO___redArg___closed__0();
lean_mark_persistent(l_Lean_Core_CoreM_toIO___redArg___closed__0);
l_Lean_Core_withIncRecDepth___redArg___closed__0 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__0();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__0);
l_Lean_Core_withIncRecDepth___redArg___closed__1 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__1();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__1);
l_Lean_Core_withIncRecDepth___redArg___closed__2 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__2();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__2);
l_Lean_Core_withIncRecDepth___redArg___closed__3 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__3();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__3);
l_Lean_Core_withIncRecDepth___redArg___closed__4 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__4();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__4);
l_Lean_Core_withIncRecDepth___redArg___closed__5 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__5();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__5);
l_Lean_Core_withIncRecDepth___redArg___closed__6 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__6();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__6);
l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3762_ = _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3762_();
lean_mark_persistent(l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3762_);
l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3762_ = _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3762_();
lean_mark_persistent(l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3762_);
l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3762_ = _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3762_();
lean_mark_persistent(l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3762_);
l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3762_ = _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3762_();
lean_mark_persistent(l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3762_);
l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3762_ = _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3762_();
lean_mark_persistent(l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3762_);
l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3762_ = _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3762_();
lean_mark_persistent(l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3762_);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3762_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_debug_moduleNameAtTimeout = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_debug_moduleNameAtTimeout);
lean_dec_ref(res);
}l_Lean_Core_throwMaxHeartbeat___redArg___closed__0 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__0();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__0);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__1 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__1();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__1);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__2 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__2();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__2);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__3 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__3();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__3);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__4 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__4();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__4);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__5 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__5();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__5);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__6 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__6();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__6);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__7 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__7();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__7);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__8 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__8();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__8);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__9 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__9();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__9);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__10 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__10();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__10);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__11 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__11();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__11);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__12 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__12();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__12);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__13 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__13();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__13);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__14 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__14();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__14);
l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__0 = _init_l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__0);
l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__1 = _init_l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__1);
l_Lean_Core_resetMessageLog___redArg___closed__0 = _init_l_Lean_Core_resetMessageLog___redArg___closed__0();
lean_mark_persistent(l_Lean_Core_resetMessageLog___redArg___closed__0);
l_Lean_Core_resetMessageLog___redArg___closed__1 = _init_l_Lean_Core_resetMessageLog___redArg___closed__1();
lean_mark_persistent(l_Lean_Core_resetMessageLog___redArg___closed__1);
l_Lean_Core_resetMessageLog___redArg___closed__2 = _init_l_Lean_Core_resetMessageLog___redArg___closed__2();
lean_mark_persistent(l_Lean_Core_resetMessageLog___redArg___closed__2);
l_Lean_Core_resetMessageLog___redArg___closed__3 = _init_l_Lean_Core_resetMessageLog___redArg___closed__3();
lean_mark_persistent(l_Lean_Core_resetMessageLog___redArg___closed__3);
l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0 = _init_l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0();
lean_mark_persistent(l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0);
l_Lean_Core_instMonadLogCoreM___lam__3___closed__0 = _init_l_Lean_Core_instMonadLogCoreM___lam__3___closed__0();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___lam__3___closed__0);
l_Lean_Core_instMonadLogCoreM___lam__3___closed__1 = _init_l_Lean_Core_instMonadLogCoreM___lam__3___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___lam__3___closed__1);
l_Lean_Core_instMonadLogCoreM___lam__3___closed__2 = _init_l_Lean_Core_instMonadLogCoreM___lam__3___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___lam__3___closed__2);
l_Lean_Core_instMonadLogCoreM___lam__3___closed__3 = _init_l_Lean_Core_instMonadLogCoreM___lam__3___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___lam__3___closed__3);
l_Lean_Core_instMonadLogCoreM___closed__0 = _init_l_Lean_Core_instMonadLogCoreM___closed__0();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___closed__0);
l_Lean_Core_instMonadLogCoreM = _init_l_Lean_Core_instMonadLogCoreM();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM);
l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4808_ = _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4808_();
lean_mark_persistent(l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4808_);
l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4808_ = _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4808_();
lean_mark_persistent(l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4808_);
l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4808_ = _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4808_();
lean_mark_persistent(l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4808_);
l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4808_ = _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4808_();
lean_mark_persistent(l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4808_);
l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4808_ = _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4808_();
lean_mark_persistent(l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4808_);
l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4808_ = _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4808_();
lean_mark_persistent(l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4808_);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_4808_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_stderrAsMessages = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_stderrAsMessages);
lean_dec_ref(res);
}l___auto___closed__0____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__0____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__0____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__1____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__1____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__1____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__2____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__2____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__2____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__3____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__3____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__3____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__4____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__4____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__4____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__5____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__5____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__5____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__6____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__6____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__6____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__7____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__7____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__7____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__8____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__8____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__8____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__9____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__9____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__9____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__10____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__10____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__10____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__11____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__11____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__11____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__12____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__12____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__12____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__13____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__13____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__13____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__14____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__14____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__14____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__15____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__15____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__15____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__16____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__16____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__16____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__17____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__17____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__17____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__18____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__18____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__18____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__19____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__19____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__19____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__20____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__20____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__20____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__21____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__21____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__21____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__22____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__22____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__22____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__23____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__23____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__23____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__24____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__24____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__24____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__25____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__25____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__25____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__26____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__26____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__26____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__27____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__27____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__27____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__28____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__28____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__28____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__29____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__29____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__29____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__30____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__30____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__30____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__31____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__31____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__31____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__32____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__32____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__32____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__33____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__33____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__33____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__34____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__34____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__34____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__35____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__35____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__35____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__36____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__36____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__36____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__37____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__37____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__37____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__38____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__38____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__38____x40_Lean_CoreM___hyg_4846_);
l___auto___closed__39____x40_Lean_CoreM___hyg_4846_ = _init_l___auto___closed__39____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto___closed__39____x40_Lean_CoreM___hyg_4846_);
l___auto____x40_Lean_CoreM___hyg_4846_ = _init_l___auto____x40_Lean_CoreM___hyg_4846_();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_4846_);
l___auto____x40_Lean_CoreM___hyg_4987_ = _init_l___auto____x40_Lean_CoreM___hyg_4987_();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_4987_);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___closed__1);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__3 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__3();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__3);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__5 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__5();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__5);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__6 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__6();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__6);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__7 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__7();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__7);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__8 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__8();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__8);
l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9 = _init_l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9);
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__0 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__0();
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__1 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__1);
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__2 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__2);
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__3 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__3);
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__4 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__4();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__4);
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__5 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__5();
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__6 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__6();
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__7 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__7();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___closed__7);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___closed__0 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___closed__0();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___closed__0);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__0 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__0);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__1);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__2);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__3);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___closed__4);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___closed__0 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___closed__0);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__1 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__1();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__1);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__2 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__2();
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__3 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__3();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__3);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__4 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__4();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__4);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__5 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__5();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__5);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__6 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__6();
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__7 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__7();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__7);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__8 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__8();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__8);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__9 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__9();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__9);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__10 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__10();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__10);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__11 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__11();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__11);
l_Lean_catchInternalIds___redArg___closed__0 = _init_l_Lean_catchInternalIds___redArg___closed__0();
lean_mark_persistent(l_Lean_catchInternalIds___redArg___closed__0);
l_Lean_mkArrow___redArg___closed__0 = _init_l_Lean_mkArrow___redArg___closed__0();
lean_mark_persistent(l_Lean_mkArrow___redArg___closed__0);
l_Lean_mkArrow___redArg___closed__1 = _init_l_Lean_mkArrow___redArg___closed__1();
lean_mark_persistent(l_Lean_mkArrow___redArg___closed__1);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28);
l___private_Lean_CoreM_0__Lean_supportedRecursors = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors);
l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0 = _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0);
l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1 = _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1);
l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2 = _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2);
l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3 = _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3);
l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0 = _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0);
l_Lean_traceBlock___redArg___lam__2___closed__0 = _init_l_Lean_traceBlock___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_traceBlock___redArg___lam__2___closed__0);
l_Lean_traceBlock___redArg___closed__0 = _init_l_Lean_traceBlock___redArg___closed__0();
lean_mark_persistent(l_Lean_traceBlock___redArg___closed__0);
l_Lean_traceBlock___redArg___closed__1 = _init_l_Lean_traceBlock___redArg___closed__1();
lean_mark_persistent(l_Lean_traceBlock___redArg___closed__1);
l_Lean_compileDecls___closed__0 = _init_l_Lean_compileDecls___closed__0();
lean_mark_persistent(l_Lean_compileDecls___closed__0);
l_Lean_compileDecls___closed__1 = _init_l_Lean_compileDecls___closed__1();
lean_mark_persistent(l_Lean_compileDecls___closed__1);
l_Lean_compileDecls___closed__2 = _init_l_Lean_compileDecls___closed__2();
lean_mark_persistent(l_Lean_compileDecls___closed__2);
l_Lean_compileDecls___closed__3 = _init_l_Lean_compileDecls___closed__3();
lean_mark_persistent(l_Lean_compileDecls___closed__3);
l_Lean_ImportM_runCoreM___redArg___closed__0 = _init_l_Lean_ImportM_runCoreM___redArg___closed__0();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__0);
l_Lean_ImportM_runCoreM___redArg___closed__1 = _init_l_Lean_ImportM_runCoreM___redArg___closed__1();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__1);
l_Lean_ImportM_runCoreM___redArg___closed__2 = _init_l_Lean_ImportM_runCoreM___redArg___closed__2();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__2);
l_Lean_ImportM_runCoreM___redArg___closed__3 = _init_l_Lean_ImportM_runCoreM___redArg___closed__3();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__3);
l_Lean_ImportM_runCoreM___redArg___closed__4 = _init_l_Lean_ImportM_runCoreM___redArg___closed__4();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__4);
l_Lean_ImportM_runCoreM___redArg___closed__5 = _init_l_Lean_ImportM_runCoreM___redArg___closed__5();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__5);
l_Lean_ImportM_runCoreM___redArg___closed__6 = _init_l_Lean_ImportM_runCoreM___redArg___closed__6();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__6);
l_Lean_ImportM_runCoreM___redArg___closed__7 = _init_l_Lean_ImportM_runCoreM___redArg___closed__7();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__7);
l_Lean_ImportM_runCoreM___redArg___closed__8 = _init_l_Lean_ImportM_runCoreM___redArg___closed__8();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__8);
l_Lean_ImportM_runCoreM___redArg___closed__9 = _init_l_Lean_ImportM_runCoreM___redArg___closed__9();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__9);
l_Lean_ImportM_runCoreM___redArg___closed__10 = _init_l_Lean_ImportM_runCoreM___redArg___closed__10();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__10);
l_Lean_ImportM_runCoreM___redArg___closed__11 = _init_l_Lean_ImportM_runCoreM___redArg___closed__11();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__11);
l_Lean_ImportM_runCoreM___redArg___closed__12 = _init_l_Lean_ImportM_runCoreM___redArg___closed__12();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__12);
l_Lean_ImportM_runCoreM___redArg___closed__13 = _init_l_Lean_ImportM_runCoreM___redArg___closed__13();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__13);
l_Lean_ImportM_runCoreM___redArg___closed__14 = _init_l_Lean_ImportM_runCoreM___redArg___closed__14();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__14);
l_Lean_ImportM_runCoreM___redArg___closed__15 = _init_l_Lean_ImportM_runCoreM___redArg___closed__15();
l_Lean_ImportM_runCoreM___redArg___closed__16 = _init_l_Lean_ImportM_runCoreM___redArg___closed__16();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__16);
l_Lean_instMonadExceptOfExceptionCoreM___closed__0 = _init_l_Lean_instMonadExceptOfExceptionCoreM___closed__0();
lean_mark_persistent(l_Lean_instMonadExceptOfExceptionCoreM___closed__0);
l_Lean_instMonadExceptOfExceptionCoreM = _init_l_Lean_instMonadExceptOfExceptionCoreM();
lean_mark_persistent(l_Lean_instMonadExceptOfExceptionCoreM);
l_Lean_instMonadRuntimeExceptionCoreM___closed__0 = _init_l_Lean_instMonadRuntimeExceptionCoreM___closed__0();
lean_mark_persistent(l_Lean_instMonadRuntimeExceptionCoreM___closed__0);
l_Lean_instMonadRuntimeExceptionCoreM = _init_l_Lean_instMonadRuntimeExceptionCoreM();
lean_mark_persistent(l_Lean_instMonadRuntimeExceptionCoreM);
l___private_Lean_CoreM_0__Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7148_ = _init_l___private_Lean_CoreM_0__Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7148_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7148_);
l___private_Lean_CoreM_0__Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7148_ = _init_l___private_Lean_CoreM_0__Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7148_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7148_);
l___private_Lean_CoreM_0__Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7148_ = _init_l___private_Lean_CoreM_0__Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7148_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7148_);
l___private_Lean_CoreM_0__Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7148_ = _init_l___private_Lean_CoreM_0__Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7148_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7148_);
l___private_Lean_CoreM_0__Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7148_ = _init_l___private_Lean_CoreM_0__Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7148_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7148_);
l___private_Lean_CoreM_0__Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7148_ = _init_l___private_Lean_CoreM_0__Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7148_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7148_);
if (builtin) {res = l___private_Lean_CoreM_0__Lean_initFn____x40_Lean_CoreM___hyg_7148_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
