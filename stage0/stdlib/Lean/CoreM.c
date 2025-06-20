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
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM;
static lean_object* l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3750_;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2;
static double l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__6;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_153_;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3;
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__26____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__1;
static lean_object* l_Lean_Core_instMonadCoreM___closed__1;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls_doCompile___closed__1;
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_153_;
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5_;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__8____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_912_(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__39____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_912_;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__0;
static lean_object* l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3750_;
LEAN_EXPORT lean_object* l_Lean_traceBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__5;
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_153_;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantVal_instantiateTypeLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7566_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5_(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__3;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4776_;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lam__3___closed__4;
double lean_float_div(double, double);
lean_object* lean_io_get_tid(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_DeclNameGenerator_mkUniqueName_isConflict(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_114_;
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Core_instantiateValueLevelParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__3(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__5;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_80_;
static lean_object* l_Lean_Core_instAddMessageContextCoreM___closed__0;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_192_;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_80_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7566_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_saveState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_153_;
static lean_object* l_Lean_useDiagnosticMsg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_40_;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isRealizing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__2____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__2;
static lean_object* l___auto___closed__16____x40_Lean_CoreM___hyg_4814_;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26;
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3750_;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_192_;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__3;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__17____x40_Lean_CoreM___hyg_4814_;
static lean_object* l___auto___closed__3____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7566_;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1;
static lean_object* l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM;
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9;
uint8_t lean_float_decLt(double, double);
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__0;
static lean_object* l_Lean_catchInternalIds___redArg___closed__0;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l___auto___closed__35____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_Core_instAddMessageContextCoreM___closed__1;
static lean_object* l___auto___closed__25____x40_Lean_CoreM___hyg_4814_;
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0;
static lean_object* l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4776_;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5857_;
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_lcnf_compile_decls(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs___boxed(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_compileDecls___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__4;
static lean_object* l___auto___closed__4____x40_Lean_CoreM___hyg_4814_;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2;
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__0;
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__10;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__12;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__14;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_912_;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_mkArrow___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCache___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_traceBlock___redArg___closed__1;
static lean_object* l___auto___closed__19____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_153_;
static lean_object* l_Lean_Core_instMonadLiftIOCoreM___closed__0;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3750_;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCache___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_80_;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_CancelToken_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__33____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__3;
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__36____x40_Lean_CoreM___hyg_4814_;
uint8_t l_Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___closed__0;
static lean_object* l_Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_912_;
static lean_object* l___auto___closed__27____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_192_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4776_;
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__20____x40_Lean_CoreM___hyg_4814_;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_curr(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_912_;
static size_t l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4776_;
static lean_object* l_Lean_useDiagnosticMsg___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM;
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_IO_addHeartbeats(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__11____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__4;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__9;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__3;
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__4;
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__7;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(size_t, size_t, lean_object*);
static uint8_t l_Lean_ImportM_runCoreM___redArg___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_async;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3;
static uint64_t l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__6;
LEAN_EXPORT uint8_t l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_80_;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instantiateValueLevelParams___closed__0;
static lean_object* l_Lean_Core_getMaxHeartbeats___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDeclsOld___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_40_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__13;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionCoreM;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5857_;
static lean_object* l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_40_;
static lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___closed__1;
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114_(lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_curr___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__1____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__1;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkChild(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_DeclNameGenerator_mkUniqueName_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_compileDecls_doCompile___lam__0(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDiag___boxed(lean_object*);
extern lean_object* l_Lean_warningAsError;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__9;
LEAN_EXPORT lean_object* l___auto____x40_Lean_CoreM___hyg_4814_;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17;
lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams_x21(lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5857_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg(lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__0;
static lean_object* l___auto___closed__30____x40_Lean_CoreM___hyg_4814_;
static lean_object* l___auto___closed__0____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4776_;
static lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
lean_object* l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_30____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___auto___closed__7____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_useDiagnosticMsg___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_traceBlock___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_PromiseCheckedResult_commitChecked(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_CoreM___hyg_4955_;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__13____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__6;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l_Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__15____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7566_;
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__7;
static lean_object* l_Lean_useDiagnosticMsg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l___auto___closed__23____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__1;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashablePos___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__3;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28;
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_compileDeclsNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19;
static lean_object* l_Lean_instMonadExceptOfExceptionCoreM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__1;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__4;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_114_;
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Core_throwMaxHeartbeat___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___auto___closed__10____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclNameGenerator;
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40_(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7566_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_114_;
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lam__3___closed__0;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5857_;
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls___closed__0;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__7;
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCache___closed__2;
LEAN_EXPORT lean_object* l_Lean_compileDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__0;
static lean_object* l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4776_;
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__5____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3750_;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_114_;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Core_instMonadLogCoreM___lam__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls_doCompile___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueNat;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__31____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instantiateValueLevelParams___closed__1;
static lean_object* l_Lean_instMonadRuntimeExceptionCoreM___closed__0;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_promiseChecked(lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1;
static lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
static lean_object* l_Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_912_;
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls___closed__1;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__0;
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__2(uint8_t, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__1;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_80_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_114_;
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_isConflict___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__8;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___auto___closed__24____x40_Lean_CoreM___hyg_4814_;
lean_object* l_Lean_addMessageContextPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5857_;
static lean_object* l_Lean_mkArrow___redArg___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2;
static lean_object* l___auto___closed__22____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__34____x40_Lean_CoreM___hyg_4814_;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_compileDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7566_;
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_stderrAsMessages;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM;
static lean_object* l_Lean_traceBlock___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_diagnostics_threshold;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isRuntime___boxed(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___closed__0;
static lean_object* l___auto___closed__12____x40_Lean_CoreM___hyg_4814_;
static lean_object* l___auto___closed__6____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_192_;
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3750_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__10;
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__11;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__9____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_mkArrowN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__14____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__8;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__29____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__8;
static double l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_40_;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__2;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwInterruptException___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3750_;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
static lean_object* l_Lean_useDiagnosticMsg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_inServer;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instAddMessageContextCoreM;
static lean_object* l___auto___closed__18____x40_Lean_CoreM___hyg_4814_;
static lean_object* l_Lean_compileDecls_doCompile___closed__0;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__10;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8;
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_debug_moduleNameAtTimeout;
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_next(lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__11;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5857_;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCache;
static lean_object* l_Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__38____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_7566_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23;
LEAN_EXPORT uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_40_;
extern lean_object* l_Lean_interruptExceptionId;
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_4776_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___closed__0;
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instAddMessageContextCoreM___closed__2;
static lean_object* l_Lean_instInhabitedDeclNameGenerator___closed__0;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_192_;
lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_912_;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT(lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_maxHeartbeats;
LEAN_EXPORT lean_object* l_Lean_internal_cmdlineSnapshots;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3;
lean_object* l_Lean_MessageLog_markAllReported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getDiag(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__28____x40_Lean_CoreM___hyg_4814_;
static lean_object* l___auto___closed__32____x40_Lean_CoreM___hyg_4814_;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_CoreM_toIO___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__1___boxed(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_192_;
static lean_object* l___auto___closed__37____x40_Lean_CoreM___hyg_4814_;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__12;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(lean_object*);
static lean_object* l___auto___closed__21____x40_Lean_CoreM___hyg_4814_;
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compiler_enableNew;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5857_(lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24;
static lean_object* l_Lean_compileDecls_doCompile___lam__1___closed__0;
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diagnostics", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("collect diagnostic information", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_;
x_2 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5_;
x_3 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5_;
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_40_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("threshold", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_40_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_40_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_40_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only diagnostic counters above this threshold are reported by the definitional equality", 87, 87);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_40_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_40_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_;
x_3 = lean_unsigned_to_nat(20u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_40_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_40_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_40_;
x_3 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_40_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_40_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_80_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxHeartbeats", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_80_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_80_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_80_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum amount of heartbeats per command. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit", 126, 126);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_80_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_80_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_3 = lean_unsigned_to_nat(200000u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_80_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_80_;
x_2 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_80_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_80_;
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_80_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_114_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("async", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_114_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_114_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_114_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("perform elaboration using multiple threads where possible\n\nThis option defaults to `false` but (when not explicitly set) is overridden to `true` in the Lean language server and cmdline. Metaprogramming users driving elaboration directly via e.g. `Lean.Elab.Command.elabCommandTopLevel` can opt into asynchronous elaboration by setting this option but then are responsible for processing messages and other data not only in the resulting command state but also from async tasks in `Lean.Command.Context.snap\?` and `Lean.Command.State.snapshotTasks`.", 548, 548);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_114_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_114_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_114_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_114_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_114_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_114_;
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_114_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_153_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inServer", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_153_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_153_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_153_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true if elaboration is being run inside the Lean language server\n\nThis option is set by the file worker and should not be modified otherwise.", 141, 141);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_153_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_153_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_153_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_153_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_153_;
x_3 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_153_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_153_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_192_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_192_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cmdlineSnapshots", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_192_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_192_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_192_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_192_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduce information stored in snapshots to the minimum necessary for the cmdline driver: diagnostics per command and final full snapshot", 135, 135);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_192_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_192_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_192_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_192_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_192_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_192_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_192_;
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_192_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
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
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__2(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nAdditional diagnostic information may be available using the `set_option ", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" true` command.", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg___lam__3___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_5 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = lean_box(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__2___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lean_useDiagnosticMsg___lam__3___closed__1;
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Name_toString(x_7, x_13, x_10);
x_15 = lean_string_append(x_11, x_14);
lean_dec(x_14);
x_16 = l_Lean_useDiagnosticMsg___lam__3___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_box(x_5);
x_22 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__2___boxed), 2, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Lean_useDiagnosticMsg___lam__3___closed__1;
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Name_toString(x_20, x_25, x_22);
x_27 = lean_string_append(x_23, x_26);
lean_dec(x_26);
x_28 = l_Lean_useDiagnosticMsg___lam__3___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_MessageData_ofFormat(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_useDiagnosticMsg___lam__3___closed__4;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_2);
return x_34;
}
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__1___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__3___boxed), 2, 0);
x_4 = l_Lean_MessageData_lazy(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_useDiagnosticMsg___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_useDiagnosticMsg___lam__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lam__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclNameGenerator___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
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
lean_dec(x_1);
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
uint8_t x_3; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
lean_inc(x_1);
x_11 = l_Lean_Environment_setExporting(x_1, x_10);
x_12 = l_Lean_Environment_containsOnBranch(x_11, x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_isPrivateName(x_2);
if (x_13 == 0)
{
x_3 = x_13;
goto block_8;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_14 = l_Lean_Environment_setExporting(x_1, x_12);
lean_inc(x_2);
x_15 = l_Lean_privateToUserName(x_2);
x_16 = l_Lean_Environment_containsOnBranch(x_14, x_15);
lean_dec(x_15);
x_3 = x_16;
goto block_8;
}
}
else
{
x_3 = x_12;
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
lean_inc(x_1);
x_5 = l_Lean_Environment_setExporting(x_1, x_3);
x_6 = l_Lean_mkPrivateName(x_1, x_2);
lean_dec(x_1);
x_7 = l_Lean_Environment_containsOnBranch(x_5, x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = 0;
x_9 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(x_3, x_7, x_8, x_1);
lean_dec(x_3);
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
lean_dec(x_4);
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
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName_curr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_DeclNameGenerator_mkUniqueName_curr(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_DeclNameGenerator_mkUniqueName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
x_4 = l_Lean_DeclNameGenerator_mkUniqueName_curr(x_1, x_3, x_2);
lean_inc(x_1);
x_5 = l_Lean_DeclNameGenerator_mkUniqueName_isConflict(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
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
lean_inc(x_1);
x_7 = l_Lean_Loop_forIn_loop___at___Lean_DeclNameGenerator_mkUniqueName_spec__0(x_1, x_6, x_2);
x_8 = l_Lean_DeclNameGenerator_mkUniqueName_curr(x_1, x_7, x_6);
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_inc(x_1);
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
lean_dec(x_7);
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
lean_dec(x_1);
lean_inc(x_5);
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
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
lean_inc(x_6);
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
lean_dec(x_3);
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
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
lean_inc(x_3);
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
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_withDeclNameForAuxNaming___redArg___lam__0___boxed), 1, 0);
lean_inc(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_withDeclNameForAuxNaming___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_5);
lean_inc(x_7);
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
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withDeclNameForAuxNaming___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
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
static lean_object* _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Kernel", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Core", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_912_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_912_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_912_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_2 = l_Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_912_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CoreM", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_912_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_912_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_912_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(912u);
x_2 = l_Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_912_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_912_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_912_;
x_3 = lean_box(0);
x_4 = l_Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_912_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
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
x_3 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_1, x_2);
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
lean_inc(x_6);
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
lean_inc(x_19);
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
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 4);
lean_inc(x_36);
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
lean_inc(x_33);
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
lean_dec(x_3);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadEnvCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_1);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_76; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
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
lean_inc(x_24);
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
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_apply_1(x_4, x_14);
x_28 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_29 = l_Lean_Option_get___redArg(x_1, x_27, x_28);
x_76 = l_Lean_Kernel_isDiagnosticsEnabled(x_26);
lean_dec(x_26);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = lean_unbox(x_29);
if (x_77 == 0)
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
goto block_75;
}
}
else
{
uint8_t x_78; 
x_78 = lean_unbox(x_29);
if (x_78 == 0)
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
lean_dec(x_50);
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
lean_dec(x_59);
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
lean_dec(x_73);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_64; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_KVMap_instValueBool;
x_10 = l_Lean_KVMap_instValueNat;
x_11 = lean_st_ref_get(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
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
lean_inc(x_27);
lean_dec(x_12);
x_28 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_29 = l_Lean_Option_get___redArg(x_9, x_16, x_28);
x_64 = l_Lean_Kernel_isDiagnosticsEnabled(x_27);
lean_dec(x_27);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = lean_unbox(x_29);
if (x_65 == 0)
{
x_30 = x_3;
x_31 = x_13;
goto block_37;
}
else
{
goto block_63;
}
}
else
{
uint8_t x_66; 
x_66 = lean_unbox(x_29);
if (x_66 == 0)
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
lean_dec(x_38);
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
lean_dec(x_47);
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
lean_dec(x_61);
x_30 = x_3;
x_31 = x_62;
goto block_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_77; 
x_6 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_KVMap_instValueBool;
x_11 = l_Lean_KVMap_instValueNat;
x_12 = lean_st_ref_get(x_4, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
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
lean_inc(x_28);
lean_dec(x_13);
x_29 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_30 = l_Lean_Option_get___redArg(x_10, x_17, x_29);
x_77 = l_Lean_Kernel_isDiagnosticsEnabled(x_28);
lean_dec(x_28);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = lean_unbox(x_30);
if (x_78 == 0)
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
goto block_76;
}
}
else
{
uint8_t x_79; 
x_79 = lean_unbox(x_30);
if (x_79 == 0)
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
lean_dec(x_51);
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
lean_dec(x_60);
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
lean_dec(x_74);
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
lean_inc(x_6);
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
lean_inc(x_22);
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
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 4);
lean_inc(x_42);
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
lean_inc(x_39);
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRecDepthCoreM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadResolveNameCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_45);
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
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
lean_inc(x_60);
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
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Environment_mainModule(x_7);
lean_dec(x_7);
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
x_12 = l_Lean_Environment_mainModule(x_11);
lean_dec(x_11);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadQuotationCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_10 = lean_ctor_get(x_8, 7);
lean_inc(x_10);
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
lean_dec(x_5);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadInfoTreeCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_4);
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
lean_dec(x_5);
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
lean_dec(x_2);
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
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
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
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
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
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
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
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
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
lean_dec(x_2);
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
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
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
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
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
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
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
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
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
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_level_eq(x_9, x_11);
if (x_13 == 0)
{
return x_13;
}
else
{
x_1 = x_10;
x_2 = x_12;
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
lean_inc(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_83; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_inc(x_12);
x_83 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_11, x_12);
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
lean_dec(x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_2, x_85);
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
lean_dec(x_1);
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
lean_inc(x_17);
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
lean_inc(x_25);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_2);
x_26 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_24, x_12, x_15);
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
lean_inc(x_34);
lean_ctor_set(x_15, 1, x_34);
lean_ctor_set(x_15, 0, x_2);
x_35 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_32, x_12, x_15);
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
lean_inc(x_49);
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
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
lean_inc(x_52);
lean_ctor_set(x_15, 1, x_52);
lean_ctor_set(x_15, 0, x_2);
x_53 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_49, x_12, x_15);
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
lean_inc(x_61);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_16, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_16, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_16, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_16, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_16, 7);
lean_inc(x_67);
x_68 = lean_ctor_get(x_16, 8);
lean_inc(x_68);
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
lean_inc(x_70);
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
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
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_70, x_12, x_74);
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
lean_inc(x_89);
lean_dec(x_7);
x_90 = lean_ctor_get(x_1, 0);
lean_inc(x_90);
lean_inc(x_90);
x_120 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_89, x_90);
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
lean_dec(x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_2, x_122);
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
lean_dec(x_1);
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
lean_inc(x_95);
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
lean_inc(x_98);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_94, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_94, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_94, 7);
lean_inc(x_104);
x_105 = lean_ctor_get(x_94, 8);
lean_inc(x_105);
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
lean_inc(x_107);
x_108 = lean_ctor_get(x_95, 1);
lean_inc(x_108);
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
lean_inc(x_110);
if (lean_is_scalar(x_97)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_97;
}
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_107, x_90, x_111);
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
LEAN_EXPORT lean_object* l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_1, x_2);
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
lean_dec(x_3);
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
x_1 = lean_box(0);
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
lean_inc(x_8);
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
lean_inc(x_16);
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
x_1 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_st_ref_get(x_4, x_5);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 5);
lean_inc(x_97);
lean_dec(x_96);
x_98 = !lean_is_exclusive(x_95);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_95, 1);
x_100 = lean_ctor_get(x_95, 0);
lean_dec(x_100);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_102 = l_Lean_ConstantInfo_name(x_1);
x_103 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_101, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_free_object(x_95);
x_6 = x_3;
x_7 = x_4;
x_8 = x_99;
goto block_94;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_2, x_105);
lean_dec(x_105);
if (x_107 == 0)
{
lean_dec(x_106);
lean_free_object(x_95);
x_6 = x_3;
x_7 = x_4;
x_8 = x_99;
goto block_94;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_95, 0, x_106);
return x_95;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_95, 1);
lean_inc(x_108);
lean_dec(x_95);
x_109 = lean_ctor_get(x_97, 1);
lean_inc(x_109);
lean_dec(x_97);
x_110 = l_Lean_ConstantInfo_name(x_1);
x_111 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_109, x_110);
if (lean_obj_tag(x_111) == 0)
{
x_6 = x_3;
x_7 = x_4;
x_8 = x_108;
goto block_94;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_2, x_113);
lean_dec(x_113);
if (x_115 == 0)
{
lean_dec(x_114);
x_6 = x_3;
x_7 = x_4;
x_8 = x_108;
goto block_94;
}
else
{
lean_object* x_116; 
lean_dec(x_2);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_108);
return x_116;
}
}
}
block_94:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_ConstantInfo_hasValue(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_12 = l_Lean_Core_instantiateValueLevelParams___closed__1;
x_13 = l_Lean_ConstantInfo_name(x_1);
x_14 = l_Lean_MessageData_ofName(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Core_instantiateValueLevelParams___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_17, x_6, x_7, x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_st_ref_take(x_7, x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 5);
lean_inc(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 5);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_2);
x_33 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_34 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_33);
lean_ctor_set(x_23, 1, x_33);
lean_ctor_set(x_23, 0, x_2);
x_35 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_32, x_34, x_23);
lean_ctor_set(x_25, 1, x_35);
x_36 = lean_st_ref_set(x_7, x_24, x_27);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_33);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
lean_inc(x_2);
x_43 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_44 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_43);
lean_ctor_set(x_23, 1, x_43);
lean_ctor_set(x_23, 0, x_2);
x_45 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_42, x_44, x_23);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_24, 5, x_46);
x_47 = lean_st_ref_set(x_7, x_24, x_27);
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
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
x_53 = lean_ctor_get(x_24, 2);
x_54 = lean_ctor_get(x_24, 3);
x_55 = lean_ctor_get(x_24, 4);
x_56 = lean_ctor_get(x_24, 6);
x_57 = lean_ctor_get(x_24, 7);
x_58 = lean_ctor_get(x_24, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_59 = lean_ctor_get(x_25, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_25, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_61 = x_25;
} else {
 lean_dec_ref(x_25);
 x_61 = lean_box(0);
}
lean_inc(x_2);
x_62 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_63 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_62);
lean_ctor_set(x_23, 1, x_62);
lean_ctor_set(x_23, 0, x_2);
x_64 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_60, x_63, x_23);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_66, 0, x_51);
lean_ctor_set(x_66, 1, x_52);
lean_ctor_set(x_66, 2, x_53);
lean_ctor_set(x_66, 3, x_54);
lean_ctor_set(x_66, 4, x_55);
lean_ctor_set(x_66, 5, x_65);
lean_ctor_set(x_66, 6, x_56);
lean_ctor_set(x_66, 7, x_57);
lean_ctor_set(x_66, 8, x_58);
x_67 = lean_st_ref_set(x_7, x_66, x_27);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_62);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_71 = lean_ctor_get(x_23, 1);
lean_inc(x_71);
lean_dec(x_23);
x_72 = lean_ctor_get(x_24, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_24, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_24, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_24, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_24, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_24, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_24, 7);
lean_inc(x_78);
x_79 = lean_ctor_get(x_24, 8);
lean_inc(x_79);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 lean_ctor_release(x_24, 6);
 lean_ctor_release(x_24, 7);
 lean_ctor_release(x_24, 8);
 x_80 = x_24;
} else {
 lean_dec_ref(x_24);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_25, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_25, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_83 = x_25;
} else {
 lean_dec_ref(x_25);
 x_83 = lean_box(0);
}
lean_inc(x_2);
x_84 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_85 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_2);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_82, x_85, x_86);
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_80)) {
 x_89 = lean_alloc_ctor(0, 9, 0);
} else {
 x_89 = x_80;
}
lean_ctor_set(x_89, 0, x_72);
lean_ctor_set(x_89, 1, x_73);
lean_ctor_set(x_89, 2, x_74);
lean_ctor_set(x_89, 3, x_75);
lean_ctor_set(x_89, 4, x_76);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set(x_89, 6, x_77);
lean_ctor_set(x_89, 7, x_78);
lean_ctor_set(x_89, 8, x_79);
x_90 = lean_st_ref_set(x_7, x_89, x_71);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_93, 1, x_91);
return x_93;
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
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateValueLevelParams(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_liftIOCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_10 = lean_ctor_get(x_8, 4);
lean_inc(x_10);
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
lean_inc(x_4);
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
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_10);
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
lean_dec(x_39);
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
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
lean_dec(x_1);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_set(x_4, x_60, x_5);
lean_dec(x_4);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
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
lean_dec(x_4);
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_SavedState_restore(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_4);
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
lean_dec(x_11);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Environment_mainModule(x_16);
lean_dec(x_16);
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
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Environment_mainModule(x_21);
lean_dec(x_21);
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
lean_dec(x_37);
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
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lean_Environment_mainModule(x_43);
lean_dec(x_43);
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
lean_dec(x_2);
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
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_82; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
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
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
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
lean_inc(x_31);
lean_dec(x_15);
x_32 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_33 = l_Lean_Option_get___redArg(x_12, x_20, x_32);
x_82 = l_Lean_Kernel_isDiagnosticsEnabled(x_31);
lean_dec(x_31);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = lean_unbox(x_33);
if (x_83 == 0)
{
lean_inc(x_6);
x_34 = x_6;
x_35 = x_16;
goto block_55;
}
else
{
goto block_81;
}
}
else
{
uint8_t x_84; 
x_84 = lean_unbox(x_33);
if (x_84 == 0)
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
lean_dec(x_40);
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
lean_dec(x_56);
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
lean_dec(x_65);
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
lean_dec(x_79);
lean_inc(x_6);
x_34 = x_6;
x_35 = x_80;
goto block_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_95; 
x_6 = lean_st_mk_ref(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
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
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
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
lean_inc(x_32);
lean_dec(x_16);
x_33 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_34 = l_Lean_Option_get___redArg(x_13, x_21, x_33);
x_95 = l_Lean_Kernel_isDiagnosticsEnabled(x_32);
lean_dec(x_32);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = lean_unbox(x_34);
if (x_96 == 0)
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
goto block_94;
}
}
else
{
uint8_t x_97; 
x_97 = lean_unbox(x_34);
if (x_97 == 0)
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
lean_dec(x_53);
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
lean_dec(x_69);
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
lean_dec(x_78);
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
lean_dec(x_92);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_74; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_KVMap_instValueBool;
x_13 = l_Lean_KVMap_instValueNat;
x_14 = lean_st_ref_get(x_6, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
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
lean_inc(x_30);
lean_dec(x_15);
x_31 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_32 = l_Lean_Option_get___redArg(x_12, x_19, x_31);
x_74 = l_Lean_Kernel_isDiagnosticsEnabled(x_30);
lean_dec(x_30);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = lean_unbox(x_32);
if (x_75 == 0)
{
lean_inc(x_6);
x_33 = x_6;
x_34 = x_16;
goto block_47;
}
else
{
goto block_73;
}
}
else
{
uint8_t x_76; 
x_76 = lean_unbox(x_32);
if (x_76 == 0)
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
lean_dec(x_39);
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
lean_dec(x_48);
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
lean_dec(x_57);
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
lean_dec(x_71);
lean_inc(x_6);
x_33 = x_6;
x_34 = x_72;
goto block_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_87; 
x_6 = lean_st_mk_ref(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_KVMap_instValueBool;
x_14 = l_Lean_KVMap_instValueNat;
x_15 = lean_st_ref_get(x_7, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
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
lean_inc(x_31);
lean_dec(x_16);
x_32 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_33 = l_Lean_Option_get___redArg(x_13, x_20, x_32);
x_87 = l_Lean_Kernel_isDiagnosticsEnabled(x_31);
lean_dec(x_31);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = lean_unbox(x_33);
if (x_88 == 0)
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
goto block_86;
}
}
else
{
uint8_t x_89; 
x_89 = lean_unbox(x_33);
if (x_89 == 0)
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
lean_dec(x_52);
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
lean_dec(x_61);
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
lean_dec(x_70);
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
lean_dec(x_84);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_105; 
x_5 = lean_io_get_num_heartbeats(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_mk_ref(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_12 = lean_st_ref_get(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
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
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
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
lean_inc(x_33);
lean_dec(x_18);
x_34 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_35 = l_Lean_Option_get___redArg(x_15, x_23, x_34);
x_105 = l_Lean_Kernel_isDiagnosticsEnabled(x_33);
lean_dec(x_33);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = lean_unbox(x_35);
if (x_106 == 0)
{
lean_inc(x_9);
x_36 = x_9;
x_37 = x_19;
goto block_78;
}
else
{
goto block_104;
}
}
else
{
uint8_t x_107; 
x_107 = lean_unbox(x_35);
if (x_107 == 0)
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
lean_dec(x_42);
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
lean_dec(x_42);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
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
lean_dec(x_53);
x_67 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_68 = l_Nat_reprFast(x_66);
x_69 = lean_string_append(x_67, x_68);
lean_dec(x_68);
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
lean_dec(x_53);
x_73 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_74 = l_Nat_reprFast(x_72);
x_75 = lean_string_append(x_73, x_74);
lean_dec(x_74);
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
lean_dec(x_79);
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
lean_dec(x_88);
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
lean_dec(x_102);
lean_inc(x_9);
x_36 = x_9;
x_37 = x_103;
goto block_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_118; 
x_6 = lean_io_get_num_heartbeats(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_mk_ref(x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_13 = lean_st_ref_get(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
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
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
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
lean_inc(x_34);
lean_dec(x_19);
x_35 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_36 = l_Lean_Option_get___redArg(x_16, x_24, x_35);
x_118 = l_Lean_Kernel_isDiagnosticsEnabled(x_34);
lean_dec(x_34);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = lean_unbox(x_36);
if (x_119 == 0)
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
goto block_117;
}
}
else
{
uint8_t x_120; 
x_120 = lean_unbox(x_36);
if (x_120 == 0)
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
lean_dec(x_55);
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
lean_dec(x_55);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
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
lean_dec(x_66);
x_80 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_81 = l_Nat_reprFast(x_79);
x_82 = lean_string_append(x_80, x_81);
lean_dec(x_81);
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
lean_dec(x_66);
x_86 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_87 = l_Nat_reprFast(x_85);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
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
lean_dec(x_92);
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
lean_dec(x_101);
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
lean_dec(x_115);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
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
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_19 = lean_ctor_get(x_4, 11);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_21 = lean_ctor_get(x_4, 12);
lean_inc(x_21);
x_22 = lean_nat_dec_eq(x_10, x_11);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_2);
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
lean_dec(x_21);
lean_dec(x_19);
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
lean_inc(x_9);
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
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
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
lean_inc(x_34);
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
lean_inc(x_52);
lean_dec(x_1);
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_dec(x_2);
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
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 4);
lean_inc(x_63);
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
lean_inc(x_60);
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
lean_inc(x_80);
lean_dec(x_1);
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
lean_dec(x_2);
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
lean_inc(x_9);
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
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_22);
x_26 = lean_st_ref_get(x_25, x_3);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_26);
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
lean_inc(x_43);
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
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_56);
x_60 = lean_st_ref_get(x_59, x_3);
lean_dec(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_60);
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
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 4);
lean_inc(x_79);
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
lean_inc(x_76);
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
lean_dec(x_90);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_91);
x_95 = lean_st_ref_get(x_94, x_3);
lean_dec(x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_90);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_95);
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
static lean_object* _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3750_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3750_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moduleNameAtTimeout", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3750_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3750_;
x_2 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3750_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3750_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("include module name in deterministic timeout error messages.\nRemark: we set this option to false to increase the stability of our test suite", 140, 140);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3750_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3750_;
x_2 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3750_;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3750_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3750_;
x_2 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3750_;
x_3 = l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_912_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3750_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3750_;
x_3 = l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3750_;
x_4 = l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3750_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Core_throwMaxHeartbeat___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
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
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_80_;
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
x_1 = lean_mk_string_unchecked(") has been reached\nUse `set_option ", 35, 35);
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
x_1 = lean_mk_string_unchecked(" <num>` to set the limit.", 25, 25);
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
x_1 = l_Lean_Core_debug_moduleNameAtTimeout;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" at `", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__12() {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_35; uint8_t x_36; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 5);
x_35 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__10;
x_36 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_6, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_8 = x_37;
goto block_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_alloc_closure((void*)(l_Lean_Core_throwMaxHeartbeat___redArg___lam__0___boxed), 1, 0);
x_39 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__11;
x_40 = l_Lean_Name_toString(x_1, x_36, x_38);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_42 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__12;
x_43 = lean_string_append(x_41, x_42);
x_8 = x_43;
goto block_34;
}
block_34:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__1;
x_10 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__3;
x_11 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
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
x_23 = l_Lean_MessageData_ofName(x_2);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__9;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_useDiagnosticMsg;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Core_instantiateValueLevelParams___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_7);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_5);
return x_33;
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
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Core_throwMaxHeartbeat___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_throwMaxHeartbeat___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
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
lean_dec(x_4);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_4);
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
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 9);
x_5 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_80_;
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
lean_dec(x_2);
return x_4;
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
lean_dec(x_8);
x_12 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
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
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkSystem(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
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
lean_dec(x_4);
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
lean_dec(x_2);
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
x_1 = lean_box(0);
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
lean_dec(x_1);
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
x_9 = lean_ctor_get(x_7, 6);
lean_inc(x_9);
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
lean_dec(x_1);
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
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 6);
lean_inc(x_7);
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
lean_inc(x_20);
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
lean_dec(x_1);
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
lean_dec(x_3);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_MessageLog_hasErrors(x_7);
lean_dec(x_7);
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
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_MessageLog_hasErrors(x_12);
lean_dec(x_12);
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
x_10 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_;
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
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
default: 
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
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
lean_dec(x_1);
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
lean_inc(x_60);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_48, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_48, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_48, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_48, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_48, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_48, 7);
lean_inc(x_67);
x_68 = lean_ctor_get(x_48, 8);
lean_inc(x_68);
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
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 2);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_85 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_86 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_87 = lean_ctor_get(x_1, 3);
lean_inc(x_87);
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
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_79, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_79, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_79, 5);
lean_inc(x_97);
x_98 = lean_ctor_get(x_79, 6);
lean_inc(x_98);
x_99 = lean_ctor_get(x_79, 7);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 8);
lean_inc(x_100);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
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
lean_dec(x_2);
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
lean_dec(x_4);
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
lean_dec(x_2);
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
lean_dec(x_7);
x_9 = lean_apply_4(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_70; 
x_18 = lean_st_mk_ref(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_22 = lean_st_ref_get(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_19, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_3);
lean_closure_set(x_29, 2, x_16);
x_30 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_31 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_4, x_30);
x_70 = l_Lean_Kernel_isDiagnosticsEnabled(x_28);
lean_dec(x_28);
if (x_70 == 0)
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
goto block_69;
}
}
else
{
if (x_31 == 0)
{
goto block_69;
}
else
{
lean_inc(x_19);
x_32 = x_19;
x_33 = x_27;
goto block_45;
}
}
block_45:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_35 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_4, x_34);
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
lean_dec(x_37);
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
block_69:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_st_ref_take(x_19, x_27);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 5);
lean_dec(x_51);
x_52 = l_Lean_Kernel_enableDiag(x_50, x_31);
x_53 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_47, 5, x_53);
lean_ctor_set(x_47, 0, x_52);
x_54 = lean_st_ref_set(x_19, x_47, x_48);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
lean_inc(x_19);
x_32 = x_19;
x_33 = x_55;
goto block_45;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_47, 1);
x_58 = lean_ctor_get(x_47, 2);
x_59 = lean_ctor_get(x_47, 3);
x_60 = lean_ctor_get(x_47, 4);
x_61 = lean_ctor_get(x_47, 6);
x_62 = lean_ctor_get(x_47, 7);
x_63 = lean_ctor_get(x_47, 8);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_64 = l_Lean_Kernel_enableDiag(x_56, x_31);
x_65 = l_Lean_Core_instInhabitedCache___closed__2;
x_66 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_57);
lean_ctor_set(x_66, 2, x_58);
lean_ctor_set(x_66, 3, x_59);
lean_ctor_set(x_66, 4, x_60);
lean_ctor_set(x_66, 5, x_65);
lean_ctor_set(x_66, 6, x_61);
lean_ctor_set(x_66, 7, x_62);
lean_ctor_set(x_66, 8, x_63);
x_67 = lean_st_ref_set(x_19, x_66, x_48);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_19);
x_32 = x_19;
x_33 = x_68;
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
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_DeclNameGenerator_mkChild(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_4, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
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
lean_dec(x_18);
x_20 = lean_st_ref_get(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
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
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
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
lean_dec(x_3);
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
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
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
lean_dec(x_3);
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
lean_inc(x_68);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_21, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_21, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_21, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_21, 6);
lean_inc(x_73);
x_74 = lean_ctor_get(x_21, 7);
lean_inc(x_74);
x_75 = lean_ctor_get(x_21, 8);
lean_inc(x_75);
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
lean_inc(x_77);
x_78 = lean_ctor_get(x_3, 1);
lean_inc(x_78);
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
lean_dec(x_3);
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
lean_dec(x_102);
x_104 = lean_st_ref_get(x_4, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
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
lean_inc(x_111);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_105, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_105, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_105, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_105, 7);
lean_inc(x_117);
x_118 = lean_ctor_get(x_105, 8);
lean_inc(x_118);
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
lean_inc(x_120);
x_121 = lean_ctor_get(x_3, 1);
lean_inc(x_121);
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
lean_dec(x_3);
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
lean_dec(x_15);
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
static lean_object* _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4776_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stderrAsMessages", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4776_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4776_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4776_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("server", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4776_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message", 133, 133);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4776_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4776_;
x_2 = l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4776_;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4776_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4776_;
x_2 = l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_912_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_4776_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4776_;
x_3 = l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4776_;
x_4 = l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4776_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__0____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__1____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__2____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__1____x40_Lean_CoreM___hyg_4814_;
x_2 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4814_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__3____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___auto___closed__4____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto___closed__5____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__4____x40_Lean_CoreM___hyg_4814_;
x_2 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4814_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__6____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__7____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__6____x40_Lean_CoreM___hyg_4814_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__8____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto___closed__9____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__8____x40_Lean_CoreM___hyg_4814_;
x_2 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__1;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4814_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__10____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__8____x40_Lean_CoreM___hyg_4814_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__11____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__10____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__12____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__13____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__14____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__13____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__12____x40_Lean_CoreM___hyg_4814_;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4814_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__15____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto___closed__16____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__15____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__12____x40_Lean_CoreM___hyg_4814_;
x_3 = l___auto___closed__0____x40_Lean_CoreM___hyg_4814_;
x_4 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__17____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl_name%", 10, 10);
return x_1;
}
}
static lean_object* _init_l___auto___closed__18____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__17____x40_Lean_CoreM___hyg_4814_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__19____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__18____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__20____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__19____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__16____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__21____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__20____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__22____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___auto___closed__23____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__22____x40_Lean_CoreM___hyg_4814_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__24____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__23____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__21____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__25____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toString", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto___closed__26____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__25____x40_Lean_CoreM___hyg_4814_;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__27____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__26____x40_Lean_CoreM___hyg_4814_;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___auto___closed__25____x40_Lean_CoreM___hyg_4814_;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__28____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__25____x40_Lean_CoreM___hyg_4814_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__29____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l___auto___closed__28____x40_Lean_CoreM___hyg_4814_;
x_3 = l___auto___closed__27____x40_Lean_CoreM___hyg_4814_;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__30____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__29____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__24____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__31____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__30____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__14____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__32____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__31____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__11____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__33____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__32____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__9____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__34____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__33____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__35____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__34____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__7____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__36____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__35____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__37____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__36____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__5____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__38____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__37____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__3____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__39____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__38____x40_Lean_CoreM___hyg_4814_;
x_2 = l___auto___closed__2____x40_Lean_CoreM___hyg_4814_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_4814_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__39____x40_Lean_CoreM___hyg_4814_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 6);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 8);
lean_inc(x_8);
lean_dec(x_3);
x_28 = lean_string_utf8_byte_size(x_1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_45; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 5);
lean_inc(x_33);
lean_dec(x_2);
x_45 = l_Lean_Syntax_getPos_x3f(x_33, x_30);
lean_dec(x_33);
if (lean_obj_tag(x_45) == 0)
{
x_34 = x_29;
goto block_44;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_34 = x_46;
goto block_44;
}
block_44:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_35 = l_Lean_FileMap_toPosition(x_32, x_34);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_1);
x_40 = l_Lean_MessageData_ofFormat(x_39);
x_41 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*5, x_30);
x_42 = lean_unbox(x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*5 + 1, x_42);
lean_ctor_set_uint8(x_41, sizeof(void*)*5 + 2, x_30);
x_43 = l_Lean_MessageLog_add(x_41, x_7);
x_9 = x_43;
x_10 = x_5;
goto block_27;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
x_9 = x_7;
x_10 = x_5;
goto block_27;
}
block_27:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_6);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_6);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_4955_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__39____x40_Lean_CoreM___hyg_4814_;
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
lean_inc(x_8);
lean_dec(x_7);
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
lean_inc(x_11);
lean_dec(x_10);
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
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_ref_take(x_1, x_6);
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
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
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
x_2 = x_6;
goto _start;
}
else
{
return x_7;
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
lean_dec(x_2);
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
lean_dec(x_1);
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
lean_dec(x_11);
lean_dec(x_10);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = lean_array_uget(x_6, x_8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_16);
x_19 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_2, x_3, x_4, x_18, x_16, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
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
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
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
uint8_t x_32; 
lean_free_object(x_9);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_dec(x_9);
x_37 = lean_array_uget(x_6, x_8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_36);
x_38 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_2, x_3, x_4, x_37, x_36, x_10, x_11, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_36);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_inc(x_5);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = lean_usize_add(x_8, x_48);
x_8 = x_49;
x_9 = x_47;
x_12 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_16 = lean_apply_5(x_1, x_15, x_13, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_6, 0, x_20);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_6, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_6, 0, x_2);
x_26 = 1;
x_27 = lean_usize_add(x_5, x_26);
x_5 = x_27;
x_9 = x_24;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_33);
x_35 = lean_apply_5(x_1, x_34, x_33, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_33);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_inc(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_5, x_45);
x_5 = x_46;
x_6 = x_44;
x_9 = x_42;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_50 = x_35;
} else {
 lean_dec_ref(x_35);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_98; lean_object* x_99; lean_object* x_103; 
x_11 = lean_ctor_get(x_4, 5);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_14 = x_2;
} else {
 lean_dec_ref(x_2);
 x_14 = lean_box(0);
}
x_98 = l_Lean_replaceRef(x_12, x_11);
lean_dec(x_12);
x_103 = l_Lean_Syntax_getPos_x3f(x_98, x_1);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_unsigned_to_nat(0u);
x_99 = x_104;
goto block_102;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_99 = x_105;
goto block_102;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
block_97:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
x_21 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___closed__0;
x_22 = lean_array_get_size(x_19);
x_23 = lean_uint64_of_nat(x_15);
lean_dec(x_15);
x_24 = lean_uint64_of_nat(x_16);
lean_dec(x_16);
x_25 = lean_uint64_mix_hash(x_23, x_24);
x_26 = 32;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = 16;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_34 = 1;
x_35 = lean_usize_sub(x_33, x_34);
x_36 = lean_usize_land(x_32, x_35);
x_37 = lean_array_uget(x_19, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_20, x_21, x_37);
x_39 = lean_array_push(x_38, x_13);
x_40 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_20, x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_18, x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_20);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_37);
x_44 = lean_array_uset(x_19, x_36, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_44);
lean_ctor_set(x_3, 1, x_51);
lean_ctor_set(x_3, 0, x_42);
x_7 = x_3;
goto block_10;
}
else
{
lean_ctor_set(x_3, 1, x_44);
lean_ctor_set(x_3, 0, x_42);
x_7 = x_3;
goto block_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_uset(x_19, x_36, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_20, x_39, x_37);
x_55 = lean_array_uset(x_53, x_36, x_54);
lean_ctor_set(x_3, 1, x_55);
x_7 = x_3;
goto block_10;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; size_t x_70; size_t x_71; size_t x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_56 = lean_ctor_get(x_3, 0);
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_3);
lean_inc(x_16);
lean_inc(x_15);
if (lean_is_scalar(x_14)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_14;
}
lean_ctor_set(x_58, 0, x_15);
lean_ctor_set(x_58, 1, x_16);
x_59 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___closed__0;
x_60 = lean_array_get_size(x_57);
x_61 = lean_uint64_of_nat(x_15);
lean_dec(x_15);
x_62 = lean_uint64_of_nat(x_16);
lean_dec(x_16);
x_63 = lean_uint64_mix_hash(x_61, x_62);
x_64 = 32;
x_65 = lean_uint64_shift_right(x_63, x_64);
x_66 = lean_uint64_xor(x_63, x_65);
x_67 = 16;
x_68 = lean_uint64_shift_right(x_66, x_67);
x_69 = lean_uint64_xor(x_66, x_68);
x_70 = lean_uint64_to_usize(x_69);
x_71 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_72 = 1;
x_73 = lean_usize_sub(x_71, x_72);
x_74 = lean_usize_land(x_70, x_73);
x_75 = lean_array_uget(x_57, x_74);
x_76 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_58, x_59, x_75);
x_77 = lean_array_push(x_76, x_13);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_58, x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_56, x_79);
lean_dec(x_56);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_58);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_75);
x_82 = lean_array_uset(x_57, x_74, x_81);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_mul(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
x_7 = x_90;
goto block_10;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_82);
x_7 = x_91;
goto block_10;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_box(0);
x_93 = lean_array_uset(x_57, x_74, x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_58, x_77, x_75);
x_95 = lean_array_uset(x_93, x_74, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_56);
lean_ctor_set(x_96, 1, x_95);
x_7 = x_96;
goto block_10;
}
}
}
block_102:
{
lean_object* x_100; 
x_100 = l_Lean_Syntax_getTailPos_x3f(x_98, x_1);
lean_dec(x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_inc(x_99);
x_15 = x_99;
x_16 = x_99;
goto block_97;
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_15 = x_99;
x_16 = x_101;
goto block_97;
}
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_array_size(x_11);
x_15 = 0;
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(x_1, x_2, x_3, x_4, x_12, x_11, x_14, x_15, x_13, x_7, x_8, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
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
lean_dec(x_18);
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
lean_dec(x_18);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_free_object(x_5);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
x_38 = lean_array_size(x_35);
x_39 = 0;
x_40 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(x_1, x_2, x_3, x_4, x_36, x_35, x_38, x_39, x_37, x_7, x_8, x_9);
lean_dec(x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_49 = x_40;
} else {
 lean_dec_ref(x_40);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_40, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_54 = x_40;
} else {
 lean_dec_ref(x_40);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_5);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_box(x_3);
x_59 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___boxed), 6, 1);
lean_closure_set(x_59, 0, x_58);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_6);
x_62 = lean_array_size(x_57);
x_63 = 0;
x_64 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(x_59, x_60, x_57, x_62, x_63, x_61, x_7, x_8, x_9);
lean_dec(x_57);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_64, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
lean_ctor_set(x_5, 0, x_69);
lean_ctor_set(x_64, 0, x_5);
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
lean_ctor_set(x_5, 0, x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_5);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_65);
lean_free_object(x_5);
x_73 = !lean_is_exclusive(x_64);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_64, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_66, 0);
lean_inc(x_75);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_75);
return x_64;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
lean_dec(x_64);
x_77 = lean_ctor_get(x_66, 0);
lean_inc(x_77);
lean_dec(x_66);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_free_object(x_5);
x_79 = !lean_is_exclusive(x_64);
if (x_79 == 0)
{
return x_64;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_64, 0);
x_81 = lean_ctor_get(x_64, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_64);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_5, 0);
lean_inc(x_83);
lean_dec(x_5);
x_84 = lean_box(x_3);
x_85 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___boxed), 6, 1);
lean_closure_set(x_85, 0, x_84);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
x_88 = lean_array_size(x_83);
x_89 = 0;
x_90 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(x_85, x_86, x_83, x_88, x_89, x_87, x_7, x_8, x_9);
lean_dec(x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_91);
x_98 = lean_ctor_get(x_90, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_99 = x_90;
} else {
 lean_dec_ref(x_90);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_92, 0);
lean_inc(x_100);
lean_dec(x_92);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_90, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_104 = x_90;
} else {
 lean_dec_ref(x_90);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_16 = lean_apply_5(x_1, x_15, x_13, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_6, 0, x_17);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_25 = x_17;
} else {
 lean_dec_ref(x_17);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_25;
 lean_ctor_set_tag(x_26, 1);
}
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_13);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_29);
lean_ctor_set(x_6, 0, x_2);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
x_9 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
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
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_dec(x_6);
x_38 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_37);
x_39 = lean_apply_5(x_1, x_38, x_37, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
lean_inc(x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_5, x_51);
x_5 = x_52;
x_6 = x_50;
x_9 = x_48;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_98; lean_object* x_99; lean_object* x_103; 
x_11 = lean_ctor_get(x_4, 5);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_14 = x_2;
} else {
 lean_dec_ref(x_2);
 x_14 = lean_box(0);
}
x_98 = l_Lean_replaceRef(x_12, x_11);
lean_dec(x_12);
x_103 = l_Lean_Syntax_getPos_x3f(x_98, x_1);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_unsigned_to_nat(0u);
x_99 = x_104;
goto block_102;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_99 = x_105;
goto block_102;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
block_97:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
x_21 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___closed__0;
x_22 = lean_array_get_size(x_19);
x_23 = lean_uint64_of_nat(x_15);
lean_dec(x_15);
x_24 = lean_uint64_of_nat(x_16);
lean_dec(x_16);
x_25 = lean_uint64_mix_hash(x_23, x_24);
x_26 = 32;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = 16;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_34 = 1;
x_35 = lean_usize_sub(x_33, x_34);
x_36 = lean_usize_land(x_32, x_35);
x_37 = lean_array_uget(x_19, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_20, x_21, x_37);
x_39 = lean_array_push(x_38, x_13);
x_40 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_20, x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_18, x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_20);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_37);
x_44 = lean_array_uset(x_19, x_36, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_44);
lean_ctor_set(x_3, 1, x_51);
lean_ctor_set(x_3, 0, x_42);
x_7 = x_3;
goto block_10;
}
else
{
lean_ctor_set(x_3, 1, x_44);
lean_ctor_set(x_3, 0, x_42);
x_7 = x_3;
goto block_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_uset(x_19, x_36, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_20, x_39, x_37);
x_55 = lean_array_uset(x_53, x_36, x_54);
lean_ctor_set(x_3, 1, x_55);
x_7 = x_3;
goto block_10;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; size_t x_70; size_t x_71; size_t x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_56 = lean_ctor_get(x_3, 0);
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_3);
lean_inc(x_16);
lean_inc(x_15);
if (lean_is_scalar(x_14)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_14;
}
lean_ctor_set(x_58, 0, x_15);
lean_ctor_set(x_58, 1, x_16);
x_59 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___closed__0;
x_60 = lean_array_get_size(x_57);
x_61 = lean_uint64_of_nat(x_15);
lean_dec(x_15);
x_62 = lean_uint64_of_nat(x_16);
lean_dec(x_16);
x_63 = lean_uint64_mix_hash(x_61, x_62);
x_64 = 32;
x_65 = lean_uint64_shift_right(x_63, x_64);
x_66 = lean_uint64_xor(x_63, x_65);
x_67 = 16;
x_68 = lean_uint64_shift_right(x_66, x_67);
x_69 = lean_uint64_xor(x_66, x_68);
x_70 = lean_uint64_to_usize(x_69);
x_71 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_72 = 1;
x_73 = lean_usize_sub(x_71, x_72);
x_74 = lean_usize_land(x_70, x_73);
x_75 = lean_array_uget(x_57, x_74);
x_76 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_58, x_59, x_75);
x_77 = lean_array_push(x_76, x_13);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_58, x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_56, x_79);
lean_dec(x_56);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_58);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_75);
x_82 = lean_array_uset(x_57, x_74, x_81);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_mul(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
x_7 = x_90;
goto block_10;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_82);
x_7 = x_91;
goto block_10;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_box(0);
x_93 = lean_array_uset(x_57, x_74, x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_58, x_77, x_75);
x_95 = lean_array_uset(x_93, x_74, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_56);
lean_ctor_set(x_96, 1, x_95);
x_7 = x_96;
goto block_10;
}
}
}
block_102:
{
lean_object* x_100; 
x_100 = l_Lean_Syntax_getTailPos_x3f(x_98, x_1);
lean_dec(x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_inc(x_99);
x_15 = x_99;
x_16 = x_99;
goto block_97;
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_15 = x_99;
x_16 = x_101;
goto block_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_2, x_3, x_5, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
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
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(x_3);
x_22 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___lam__0___boxed), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
x_25 = lean_array_size(x_10);
x_26 = 0;
x_27 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__11(x_22, x_23, x_10, x_25, x_26, x_24, x_6, x_7, x_19);
lean_dec(x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
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
x_11 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_7);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; double x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_29 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
x_30 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___closed__0;
x_31 = lean_box(0);
lean_inc(x_1);
x_32 = lean_float_of_nat(x_1);
x_33 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_34 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_float(x_34, sizeof(void*)*2, x_32);
lean_ctor_set_float(x_34, sizeof(void*)*2 + 8, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 16, x_17);
x_35 = l_Lean_MessageData_nil;
x_36 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set_tag(x_20, 8);
lean_ctor_set(x_20, 1, x_36);
lean_ctor_set(x_20, 0, x_30);
x_37 = lean_box(0);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Elab_mkMessageCore(x_26, x_27, x_20, x_38, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_28 == 0)
{
lean_inc(x_8);
x_40 = x_8;
x_41 = x_9;
x_42 = x_10;
goto block_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_130 = lean_ctor_get(x_39, 4);
lean_inc(x_130);
x_131 = lean_box(x_3);
x_132 = lean_box(x_28);
x_133 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___lam__0___boxed), 4, 3);
lean_closure_set(x_133, 0, x_29);
lean_closure_set(x_133, 1, x_131);
lean_closure_set(x_133, 2, x_132);
x_134 = l_Lean_MessageData_hasTag(x_133, x_130);
if (x_134 == 0)
{
lean_dec(x_39);
lean_dec(x_22);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_10;
goto block_16;
}
else
{
lean_inc(x_8);
x_40 = x_8;
x_41 = x_9;
x_42 = x_10;
goto block_129;
}
}
block_129:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_st_ref_take(x_41, x_42);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
x_48 = lean_ctor_get(x_39, 4);
x_49 = lean_ctor_get(x_40, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_40, 7);
lean_inc(x_50);
lean_dec(x_40);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_46, 6);
lean_ctor_set(x_43, 1, x_50);
lean_ctor_set(x_43, 0, x_49);
if (lean_is_scalar(x_22)) {
 x_53 = lean_alloc_ctor(4, 2, 0);
} else {
 x_53 = x_22;
 lean_ctor_set_tag(x_53, 4);
}
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_39, 4, x_53);
x_54 = l_Lean_MessageLog_add(x_39, x_52);
lean_ctor_set(x_46, 6, x_54);
x_55 = lean_st_ref_set(x_41, x_46, x_47);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_56;
goto block_16;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_ctor_get(x_46, 0);
x_58 = lean_ctor_get(x_46, 1);
x_59 = lean_ctor_get(x_46, 2);
x_60 = lean_ctor_get(x_46, 3);
x_61 = lean_ctor_get(x_46, 4);
x_62 = lean_ctor_get(x_46, 5);
x_63 = lean_ctor_get(x_46, 6);
x_64 = lean_ctor_get(x_46, 7);
x_65 = lean_ctor_get(x_46, 8);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_46);
lean_ctor_set(x_43, 1, x_50);
lean_ctor_set(x_43, 0, x_49);
if (lean_is_scalar(x_22)) {
 x_66 = lean_alloc_ctor(4, 2, 0);
} else {
 x_66 = x_22;
 lean_ctor_set_tag(x_66, 4);
}
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set(x_66, 1, x_48);
lean_ctor_set(x_39, 4, x_66);
x_67 = l_Lean_MessageLog_add(x_39, x_63);
x_68 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_58);
lean_ctor_set(x_68, 2, x_59);
lean_ctor_set(x_68, 3, x_60);
lean_ctor_set(x_68, 4, x_61);
lean_ctor_set(x_68, 5, x_62);
lean_ctor_set(x_68, 6, x_67);
lean_ctor_set(x_68, 7, x_64);
lean_ctor_set(x_68, 8, x_65);
x_69 = lean_st_ref_set(x_41, x_68, x_47);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_70;
goto block_16;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_71 = lean_ctor_get(x_43, 0);
x_72 = lean_ctor_get(x_43, 1);
x_73 = lean_ctor_get(x_39, 0);
x_74 = lean_ctor_get(x_39, 1);
x_75 = lean_ctor_get(x_39, 2);
x_76 = lean_ctor_get_uint8(x_39, sizeof(void*)*5);
x_77 = lean_ctor_get_uint8(x_39, sizeof(void*)*5 + 1);
x_78 = lean_ctor_get_uint8(x_39, sizeof(void*)*5 + 2);
x_79 = lean_ctor_get(x_39, 3);
x_80 = lean_ctor_get(x_39, 4);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_39);
x_81 = lean_ctor_get(x_40, 6);
lean_inc(x_81);
x_82 = lean_ctor_get(x_40, 7);
lean_inc(x_82);
lean_dec(x_40);
x_83 = lean_ctor_get(x_71, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_71, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_71, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_71, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_71, 4);
lean_inc(x_87);
x_88 = lean_ctor_get(x_71, 5);
lean_inc(x_88);
x_89 = lean_ctor_get(x_71, 6);
lean_inc(x_89);
x_90 = lean_ctor_get(x_71, 7);
lean_inc(x_90);
x_91 = lean_ctor_get(x_71, 8);
lean_inc(x_91);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 lean_ctor_release(x_71, 6);
 lean_ctor_release(x_71, 7);
 lean_ctor_release(x_71, 8);
 x_92 = x_71;
} else {
 lean_dec_ref(x_71);
 x_92 = lean_box(0);
}
lean_ctor_set(x_43, 1, x_82);
lean_ctor_set(x_43, 0, x_81);
if (lean_is_scalar(x_22)) {
 x_93 = lean_alloc_ctor(4, 2, 0);
} else {
 x_93 = x_22;
 lean_ctor_set_tag(x_93, 4);
}
lean_ctor_set(x_93, 0, x_43);
lean_ctor_set(x_93, 1, x_80);
x_94 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_94, 0, x_73);
lean_ctor_set(x_94, 1, x_74);
lean_ctor_set(x_94, 2, x_75);
lean_ctor_set(x_94, 3, x_79);
lean_ctor_set(x_94, 4, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*5, x_76);
lean_ctor_set_uint8(x_94, sizeof(void*)*5 + 1, x_77);
lean_ctor_set_uint8(x_94, sizeof(void*)*5 + 2, x_78);
x_95 = l_Lean_MessageLog_add(x_94, x_89);
if (lean_is_scalar(x_92)) {
 x_96 = lean_alloc_ctor(0, 9, 0);
} else {
 x_96 = x_92;
}
lean_ctor_set(x_96, 0, x_83);
lean_ctor_set(x_96, 1, x_84);
lean_ctor_set(x_96, 2, x_85);
lean_ctor_set(x_96, 3, x_86);
lean_ctor_set(x_96, 4, x_87);
lean_ctor_set(x_96, 5, x_88);
lean_ctor_set(x_96, 6, x_95);
lean_ctor_set(x_96, 7, x_90);
lean_ctor_set(x_96, 8, x_91);
x_97 = lean_st_ref_set(x_41, x_96, x_72);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_98;
goto block_16;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_99 = lean_ctor_get(x_43, 0);
x_100 = lean_ctor_get(x_43, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_43);
x_101 = lean_ctor_get(x_39, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 2);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_39, sizeof(void*)*5);
x_105 = lean_ctor_get_uint8(x_39, sizeof(void*)*5 + 1);
x_106 = lean_ctor_get_uint8(x_39, sizeof(void*)*5 + 2);
x_107 = lean_ctor_get(x_39, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_39, 4);
lean_inc(x_108);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 x_109 = x_39;
} else {
 lean_dec_ref(x_39);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_40, 6);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 7);
lean_inc(x_111);
lean_dec(x_40);
x_112 = lean_ctor_get(x_99, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_99, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_99, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_99, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_99, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_99, 5);
lean_inc(x_117);
x_118 = lean_ctor_get(x_99, 6);
lean_inc(x_118);
x_119 = lean_ctor_get(x_99, 7);
lean_inc(x_119);
x_120 = lean_ctor_get(x_99, 8);
lean_inc(x_120);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 lean_ctor_release(x_99, 5);
 lean_ctor_release(x_99, 6);
 lean_ctor_release(x_99, 7);
 lean_ctor_release(x_99, 8);
 x_121 = x_99;
} else {
 lean_dec_ref(x_99);
 x_121 = lean_box(0);
}
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_110);
lean_ctor_set(x_122, 1, x_111);
if (lean_is_scalar(x_22)) {
 x_123 = lean_alloc_ctor(4, 2, 0);
} else {
 x_123 = x_22;
 lean_ctor_set_tag(x_123, 4);
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_108);
if (lean_is_scalar(x_109)) {
 x_124 = lean_alloc_ctor(0, 5, 3);
} else {
 x_124 = x_109;
}
lean_ctor_set(x_124, 0, x_101);
lean_ctor_set(x_124, 1, x_102);
lean_ctor_set(x_124, 2, x_103);
lean_ctor_set(x_124, 3, x_107);
lean_ctor_set(x_124, 4, x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*5, x_104);
lean_ctor_set_uint8(x_124, sizeof(void*)*5 + 1, x_105);
lean_ctor_set_uint8(x_124, sizeof(void*)*5 + 2, x_106);
x_125 = l_Lean_MessageLog_add(x_124, x_118);
if (lean_is_scalar(x_121)) {
 x_126 = lean_alloc_ctor(0, 9, 0);
} else {
 x_126 = x_121;
}
lean_ctor_set(x_126, 0, x_112);
lean_ctor_set(x_126, 1, x_113);
lean_ctor_set(x_126, 2, x_114);
lean_ctor_set(x_126, 3, x_115);
lean_ctor_set(x_126, 4, x_116);
lean_ctor_set(x_126, 5, x_117);
lean_ctor_set(x_126, 6, x_125);
lean_ctor_set(x_126, 7, x_119);
lean_ctor_set(x_126, 8, x_120);
x_127 = lean_st_ref_set(x_41, x_126, x_100);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_128;
goto block_16;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; double x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_135 = lean_ctor_get(x_20, 0);
x_136 = lean_ctor_get(x_20, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_20);
x_137 = lean_ctor_get(x_8, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_8, 1);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_140 = l_Lean_Core_instMonadLogCoreM___lam__3___closed__0;
x_141 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___closed__0;
x_142 = lean_box(0);
lean_inc(x_1);
x_143 = lean_float_of_nat(x_1);
x_144 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_145 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_float(x_145, sizeof(void*)*2, x_143);
lean_ctor_set_float(x_145, sizeof(void*)*2 + 8, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*2 + 16, x_17);
x_146 = l_Lean_MessageData_nil;
x_147 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_21);
x_148 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_box(0);
x_150 = lean_unbox(x_149);
x_151 = l_Lean_Elab_mkMessageCore(x_137, x_138, x_148, x_150, x_135, x_136);
lean_dec(x_136);
lean_dec(x_135);
if (x_139 == 0)
{
lean_inc(x_8);
x_152 = x_8;
x_153 = x_9;
x_154 = x_10;
goto block_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_151, 4);
lean_inc(x_188);
x_189 = lean_box(x_3);
x_190 = lean_box(x_139);
x_191 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___lam__0___boxed), 4, 3);
lean_closure_set(x_191, 0, x_140);
lean_closure_set(x_191, 1, x_189);
lean_closure_set(x_191, 2, x_190);
x_192 = l_Lean_MessageData_hasTag(x_191, x_188);
if (x_192 == 0)
{
lean_dec(x_151);
lean_dec(x_22);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_10;
goto block_16;
}
else
{
lean_inc(x_8);
x_152 = x_8;
x_153 = x_9;
x_154 = x_10;
goto block_187;
}
}
block_187:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_155 = lean_st_ref_take(x_153, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_151, 2);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_151, sizeof(void*)*5);
x_163 = lean_ctor_get_uint8(x_151, sizeof(void*)*5 + 1);
x_164 = lean_ctor_get_uint8(x_151, sizeof(void*)*5 + 2);
x_165 = lean_ctor_get(x_151, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_151, 4);
lean_inc(x_166);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 x_167 = x_151;
} else {
 lean_dec_ref(x_151);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_152, 6);
lean_inc(x_168);
x_169 = lean_ctor_get(x_152, 7);
lean_inc(x_169);
lean_dec(x_152);
x_170 = lean_ctor_get(x_156, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_156, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_156, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_156, 4);
lean_inc(x_174);
x_175 = lean_ctor_get(x_156, 5);
lean_inc(x_175);
x_176 = lean_ctor_get(x_156, 6);
lean_inc(x_176);
x_177 = lean_ctor_get(x_156, 7);
lean_inc(x_177);
x_178 = lean_ctor_get(x_156, 8);
lean_inc(x_178);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 lean_ctor_release(x_156, 3);
 lean_ctor_release(x_156, 4);
 lean_ctor_release(x_156, 5);
 lean_ctor_release(x_156, 6);
 lean_ctor_release(x_156, 7);
 lean_ctor_release(x_156, 8);
 x_179 = x_156;
} else {
 lean_dec_ref(x_156);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_158;
}
lean_ctor_set(x_180, 0, x_168);
lean_ctor_set(x_180, 1, x_169);
if (lean_is_scalar(x_22)) {
 x_181 = lean_alloc_ctor(4, 2, 0);
} else {
 x_181 = x_22;
 lean_ctor_set_tag(x_181, 4);
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_166);
if (lean_is_scalar(x_167)) {
 x_182 = lean_alloc_ctor(0, 5, 3);
} else {
 x_182 = x_167;
}
lean_ctor_set(x_182, 0, x_159);
lean_ctor_set(x_182, 1, x_160);
lean_ctor_set(x_182, 2, x_161);
lean_ctor_set(x_182, 3, x_165);
lean_ctor_set(x_182, 4, x_181);
lean_ctor_set_uint8(x_182, sizeof(void*)*5, x_162);
lean_ctor_set_uint8(x_182, sizeof(void*)*5 + 1, x_163);
lean_ctor_set_uint8(x_182, sizeof(void*)*5 + 2, x_164);
x_183 = l_Lean_MessageLog_add(x_182, x_176);
if (lean_is_scalar(x_179)) {
 x_184 = lean_alloc_ctor(0, 9, 0);
} else {
 x_184 = x_179;
}
lean_ctor_set(x_184, 0, x_170);
lean_ctor_set(x_184, 1, x_171);
lean_ctor_set(x_184, 2, x_172);
lean_ctor_set(x_184, 3, x_173);
lean_ctor_set(x_184, 4, x_174);
lean_ctor_set(x_184, 5, x_175);
lean_ctor_set(x_184, 6, x_183);
lean_ctor_set(x_184, 7, x_177);
lean_ctor_set(x_184, 8, x_178);
x_185 = lean_st_ref_set(x_153, x_184, x_157);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_186;
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
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(x_4, x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_7);
x_12 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2;
x_13 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9;
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(x_13, x_12, x_11, x_9, x_15, x_1, x_2, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_41; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_dec(x_17);
x_50 = lean_mk_empty_array_with_capacity(x_48);
lean_dec(x_48);
x_51 = lean_array_get_size(x_49);
x_52 = lean_nat_dec_lt(x_14, x_51);
if (x_52 == 0)
{
lean_dec(x_51);
lean_dec(x_49);
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
lean_dec(x_49);
x_41 = x_50;
goto block_47;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_56 = l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(x_49, x_54, x_55, x_50);
lean_dec(x_49);
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
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13(x_14, x_20, x_11, x_19, x_21, x_22, x_20, x_1, x_2, x_18);
lean_dec(x_2);
lean_dec(x_19);
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
x_33 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg(x_29, x_30, x_32);
lean_dec(x_32);
x_19 = x_33;
goto block_28;
}
block_40:
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_38, x_36);
if (x_39 == 0)
{
lean_dec(x_36);
lean_inc(x_38);
x_29 = x_35;
x_30 = x_38;
x_31 = x_37;
x_32 = x_38;
goto block_34;
}
else
{
x_29 = x_35;
x_30 = x_38;
x_31 = x_37;
x_32 = x_36;
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
x_36 = x_45;
x_37 = x_42;
x_38 = x_45;
goto block_40;
}
else
{
x_35 = x_41;
x_36 = x_45;
x_37 = x_42;
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
uint8_t x_57; 
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
return x_16;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_16, 0);
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_16);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_box(0);
lean_ctor_set(x_7, 0, x_61);
return x_7;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_7, 0);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_7);
x_64 = l_Lean_PersistentArray_isEmpty___redArg(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__2;
x_66 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__4;
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__9;
lean_inc(x_2);
lean_inc(x_1);
x_69 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(x_66, x_65, x_64, x_62, x_68, x_1, x_2, x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_93; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_100 = lean_ctor_get(x_70, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_70, 1);
lean_inc(x_101);
lean_dec(x_70);
x_102 = lean_mk_empty_array_with_capacity(x_100);
lean_dec(x_100);
x_103 = lean_array_get_size(x_101);
x_104 = lean_nat_dec_lt(x_67, x_103);
if (x_104 == 0)
{
lean_dec(x_103);
lean_dec(x_101);
x_93 = x_102;
goto block_99;
}
else
{
uint8_t x_105; 
x_105 = lean_nat_dec_le(x_103, x_103);
if (x_105 == 0)
{
lean_dec(x_103);
lean_dec(x_101);
x_93 = x_102;
goto block_99;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; 
x_106 = 0;
x_107 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_108 = l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(x_101, x_106, x_107, x_102);
lean_dec(x_101);
x_93 = x_108;
goto block_99;
}
}
block_80:
{
lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_box(0);
x_74 = lean_array_size(x_72);
x_75 = 0;
x_76 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13(x_67, x_73, x_64, x_72, x_74, x_75, x_73, x_1, x_2, x_71);
lean_dec(x_2);
lean_dec(x_72);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
block_86:
{
lean_object* x_85; 
lean_dec(x_83);
x_85 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg(x_81, x_82, x_84);
lean_dec(x_84);
x_72 = x_85;
goto block_80;
}
block_92:
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_90, x_88);
if (x_91 == 0)
{
lean_dec(x_88);
lean_inc(x_90);
x_81 = x_87;
x_82 = x_90;
x_83 = x_89;
x_84 = x_90;
goto block_86;
}
else
{
x_81 = x_87;
x_82 = x_90;
x_83 = x_89;
x_84 = x_88;
goto block_86;
}
}
block_99:
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_array_get_size(x_93);
x_95 = lean_nat_dec_eq(x_94, x_67);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_sub(x_94, x_96);
x_98 = lean_nat_dec_le(x_67, x_97);
if (x_98 == 0)
{
lean_inc(x_97);
x_87 = x_93;
x_88 = x_97;
x_89 = x_94;
x_90 = x_97;
goto block_92;
}
else
{
x_87 = x_93;
x_88 = x_97;
x_89 = x_94;
x_90 = x_67;
goto block_92;
}
}
else
{
lean_dec(x_94);
x_72 = x_93;
goto block_80;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_ctor_get(x_69, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_69, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_111 = x_69;
} else {
 lean_dec_ref(x_69);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_62);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_63);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_3);
return x_116;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_replaceRef(x_3, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_15);
x_16 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec(x_14);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_17, x_18, x_16);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_20, x_5, x_6, x_13);
lean_dec(x_5);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_6, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
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
lean_inc(x_69);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_25, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_25, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_25, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_25, 6);
lean_inc(x_74);
x_75 = lean_ctor_get(x_25, 7);
lean_inc(x_75);
x_76 = lean_ctor_get(x_25, 8);
lean_inc(x_76);
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
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
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
lean_dec(x_108);
x_112 = lean_array_size(x_111);
x_113 = 0;
x_114 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_112, x_113, x_111);
x_115 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_115, 0, x_2);
lean_ctor_set(x_115, 1, x_4);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_115, x_110, x_6, x_107);
lean_dec(x_110);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_st_ref_take(x_6, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_120, 4);
lean_inc(x_121);
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
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_120, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 5);
lean_inc(x_128);
x_129 = lean_ctor_get(x_120, 6);
lean_inc(x_129);
x_130 = lean_ctor_get(x_120, 7);
lean_inc(x_130);
x_131 = lean_ctor_get(x_120, 8);
lean_inc(x_131);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19(x_1, x_5, x_2, x_3, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(x_4, x_11);
return x_12;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__5() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__6() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHeartbeats;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; double x_14; double x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; double x_30; double x_31; lean_object* x_32; lean_object* x_43; lean_object* x_44; double x_45; uint8_t x_46; double x_47; lean_object* x_48; lean_object* x_49; lean_object* x_58; lean_object* x_59; lean_object* x_60; double x_61; uint8_t x_62; lean_object* x_63; double x_64; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; double x_82; lean_object* x_83; double x_84; lean_object* x_85; uint8_t x_86; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; double x_130; double x_131; lean_object* x_132; double x_133; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_159; lean_object* x_160; lean_object* x_161; double x_162; lean_object* x_163; uint8_t x_164; double x_165; lean_object* x_166; uint8_t x_167; lean_object* x_206; lean_object* x_207; lean_object* x_208; double x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; double x_213; double x_214; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_269; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 5);
lean_inc(x_10);
lean_inc(x_1);
x_75 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18___redArg(x_1, x_6, x_8);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_269 = lean_unbox(x_76);
if (x_269 == 0)
{
lean_object* x_270; uint8_t x_271; 
x_270 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__3;
x_271 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_9, x_270);
if (x_271 == 0)
{
lean_object* x_272; 
lean_dec(x_76);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
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
x_18 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__0;
x_19 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set_float(x_19, sizeof(void*)*2, x_18);
lean_ctor_set_float(x_19, sizeof(void*)*2 + 8, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_4);
x_20 = lean_box(0);
x_21 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___lam__0(x_11, x_10, x_16, x_12, x_19, x_20, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set_float(x_22, sizeof(void*)*2, x_15);
lean_ctor_set_float(x_22, sizeof(void*)*2 + 8, x_14);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 16, x_4);
x_23 = lean_box(0);
x_24 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___lam__0(x_11, x_10, x_16, x_12, x_22, x_23, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_12);
return x_24;
}
}
block_42:
{
lean_object* x_33; 
lean_inc(x_7);
lean_inc(x_6);
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
lean_dec(x_33);
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
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_33);
x_41 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__2;
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
x_50 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__0;
x_51 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_5);
lean_ctor_set_float(x_51, sizeof(void*)*2, x_50);
lean_ctor_set_float(x_51, sizeof(void*)*2 + 8, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 16, x_4);
x_52 = lean_box(0);
x_53 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___lam__0(x_43, x_10, x_48, x_44, x_51, x_52, x_6, x_7, x_49);
lean_dec(x_7);
lean_dec(x_44);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_5);
lean_ctor_set_float(x_54, sizeof(void*)*2, x_47);
lean_ctor_set_float(x_54, sizeof(void*)*2 + 8, x_45);
lean_ctor_set_uint8(x_54, sizeof(void*)*2 + 16, x_4);
x_55 = lean_box(0);
x_56 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___lam__0(x_43, x_10, x_48, x_44, x_54, x_55, x_6, x_7, x_49);
lean_dec(x_7);
lean_dec(x_44);
return x_56;
}
}
block_74:
{
lean_object* x_65; 
lean_inc(x_7);
lean_inc(x_6);
x_65 = lean_apply_4(x_2, x_63, x_6, x_7, x_60);
if (lean_obj_tag(x_65) == 0)
{
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_43 = x_58;
x_44 = x_59;
x_45 = x_61;
x_46 = x_62;
x_47 = x_64;
x_48 = x_66;
x_49 = x_67;
goto block_57;
}
else
{
uint8_t x_68; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_65);
x_73 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__2;
x_43 = x_58;
x_44 = x_59;
x_45 = x_61;
x_46 = x_62;
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
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_st_ref_take(x_7, x_80);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 4);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
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
x_96 = l_Lean_PersistentArray_append___redArg(x_83, x_95);
lean_dec(x_95);
lean_ctor_set(x_90, 0, x_96);
x_97 = lean_st_ref_set(x_7, x_89, x_91);
lean_dec(x_7);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(x_85, x_98);
lean_dec(x_85);
return x_99;
}
else
{
uint64_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get_uint64(x_90, sizeof(void*)*1);
x_101 = lean_ctor_get(x_90, 0);
lean_inc(x_101);
lean_dec(x_90);
x_102 = l_Lean_PersistentArray_append___redArg(x_83, x_101);
lean_dec(x_101);
x_103 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set_uint64(x_103, sizeof(void*)*1, x_100);
lean_ctor_set(x_89, 4, x_103);
x_104 = lean_st_ref_set(x_7, x_89, x_91);
lean_dec(x_7);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(x_85, x_105);
lean_dec(x_85);
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
lean_inc(x_116);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_117 = x_90;
} else {
 lean_dec_ref(x_90);
 x_117 = lean_box(0);
}
x_118 = l_Lean_PersistentArray_append___redArg(x_83, x_116);
lean_dec(x_116);
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
lean_dec(x_121);
x_123 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(x_85, x_122);
lean_dec(x_85);
return x_123;
}
}
else
{
lean_dec(x_83);
x_26 = x_78;
x_27 = x_79;
x_28 = x_80;
x_29 = x_81;
x_30 = x_82;
x_31 = x_84;
x_32 = x_85;
goto block_42;
}
}
else
{
lean_dec(x_83);
x_26 = x_78;
x_27 = x_79;
x_28 = x_80;
x_29 = x_81;
x_30 = x_82;
x_31 = x_84;
x_32 = x_85;
goto block_42;
}
}
block_136:
{
double x_134; uint8_t x_135; 
x_134 = lean_float_sub(x_130, x_131);
x_135 = lean_float_decLt(x_133, x_134);
x_78 = x_125;
x_79 = x_126;
x_80 = x_127;
x_81 = x_128;
x_82 = x_130;
x_83 = x_129;
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
lean_dec(x_143);
x_146 = lean_float_of_nat(x_138);
x_147 = lean_float_of_nat(x_144);
x_148 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__3;
x_149 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_9, x_148);
if (x_149 == 0)
{
lean_dec(x_9);
lean_inc(x_141);
x_78 = x_137;
x_79 = x_141;
x_80 = x_145;
x_81 = x_149;
x_82 = x_147;
x_83 = x_140;
x_84 = x_146;
x_85 = x_141;
x_86 = x_149;
goto block_124;
}
else
{
if (x_139 == 0)
{
lean_object* x_150; lean_object* x_151; double x_152; double x_153; double x_154; 
x_150 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__4;
x_151 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_9, x_150);
lean_dec(x_9);
x_152 = lean_float_of_nat(x_151);
x_153 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__5;
x_154 = lean_float_div(x_152, x_153);
lean_inc(x_141);
x_125 = x_137;
x_126 = x_141;
x_127 = x_145;
x_128 = x_149;
x_129 = x_140;
x_130 = x_147;
x_131 = x_146;
x_132 = x_141;
x_133 = x_154;
goto block_136;
}
else
{
lean_object* x_155; lean_object* x_156; double x_157; 
x_155 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__4;
x_156 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_9, x_155);
lean_dec(x_9);
x_157 = lean_float_of_nat(x_156);
lean_inc(x_141);
x_125 = x_137;
x_126 = x_141;
x_127 = x_145;
x_128 = x_149;
x_129 = x_140;
x_130 = x_147;
x_131 = x_146;
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
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_st_ref_take(x_7, x_161);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 4);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
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
lean_dec(x_176);
lean_ctor_set(x_171, 0, x_177);
x_178 = lean_st_ref_set(x_7, x_170, x_172);
lean_dec(x_7);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(x_166, x_179);
lean_dec(x_166);
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
lean_dec(x_182);
x_184 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set_uint64(x_184, sizeof(void*)*1, x_181);
lean_ctor_set(x_170, 4, x_184);
x_185 = lean_st_ref_set(x_7, x_170, x_172);
lean_dec(x_7);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(x_166, x_186);
lean_dec(x_166);
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
lean_inc(x_197);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_198 = x_171;
} else {
 lean_dec_ref(x_171);
 x_198 = lean_box(0);
}
x_199 = l_Lean_PersistentArray_append___redArg(x_163, x_197);
lean_dec(x_197);
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
lean_dec(x_202);
x_204 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(x_166, x_203);
lean_dec(x_166);
return x_204;
}
}
else
{
lean_dec(x_163);
x_58 = x_159;
x_59 = x_160;
x_60 = x_161;
x_61 = x_162;
x_62 = x_164;
x_63 = x_166;
x_64 = x_165;
goto block_74;
}
}
else
{
lean_dec(x_163);
x_58 = x_159;
x_59 = x_160;
x_60 = x_161;
x_61 = x_162;
x_62 = x_164;
x_63 = x_166;
x_64 = x_165;
goto block_74;
}
}
block_217:
{
double x_215; uint8_t x_216; 
x_215 = lean_float_sub(x_209, x_213);
x_216 = lean_float_decLt(x_214, x_215);
x_159 = x_206;
x_160 = x_207;
x_161 = x_208;
x_162 = x_209;
x_163 = x_210;
x_164 = x_211;
x_165 = x_213;
x_166 = x_212;
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
lean_dec(x_224);
x_227 = lean_float_of_nat(x_219);
x_228 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__6;
x_229 = lean_float_div(x_227, x_228);
x_230 = lean_float_of_nat(x_225);
x_231 = lean_float_div(x_230, x_228);
x_232 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__3;
x_233 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_9, x_232);
if (x_233 == 0)
{
lean_dec(x_9);
lean_inc(x_222);
x_159 = x_218;
x_160 = x_222;
x_161 = x_226;
x_162 = x_231;
x_163 = x_221;
x_164 = x_233;
x_165 = x_229;
x_166 = x_222;
x_167 = x_233;
goto block_205;
}
else
{
if (x_220 == 0)
{
lean_object* x_234; lean_object* x_235; double x_236; double x_237; double x_238; 
x_234 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__4;
x_235 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_9, x_234);
lean_dec(x_9);
x_236 = lean_float_of_nat(x_235);
x_237 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__5;
x_238 = lean_float_div(x_236, x_237);
lean_inc(x_222);
x_206 = x_218;
x_207 = x_222;
x_208 = x_226;
x_209 = x_231;
x_210 = x_221;
x_211 = x_233;
x_212 = x_222;
x_213 = x_229;
x_214 = x_238;
goto block_217;
}
else
{
lean_object* x_239; lean_object* x_240; double x_241; 
x_239 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__4;
x_240 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_9, x_239);
lean_dec(x_9);
x_241 = lean_float_of_nat(x_240);
lean_inc(x_222);
x_206 = x_218;
x_207 = x_222;
x_208 = x_226;
x_209 = x_231;
x_210 = x_221;
x_211 = x_233;
x_212 = x_222;
x_213 = x_229;
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
lean_dec(x_243);
x_246 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__7;
x_247 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_9, x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_io_mono_nanos_now(x_245);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_7);
lean_inc(x_6);
x_251 = lean_apply_3(x_3, x_6, x_7, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_252);
lean_inc(x_244);
x_218 = x_244;
x_219 = x_249;
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
lean_dec(x_251);
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_255);
lean_inc(x_244);
x_218 = x_244;
x_219 = x_249;
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
lean_dec(x_258);
lean_inc(x_7);
lean_inc(x_6);
x_261 = lean_apply_3(x_3, x_6, x_7, x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_262);
lean_inc(x_244);
x_137 = x_244;
x_138 = x_259;
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
lean_dec(x_261);
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_265);
lean_inc(x_244);
x_137 = x_244;
x_138 = x_259;
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
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
x_11 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_;
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
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; uint8_t x_140; uint8_t x_157; uint8_t x_158; 
x_130 = lean_box(2);
x_157 = lean_unbox(x_130);
x_158 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_3, x_157);
if (x_158 == 0)
{
x_140 = x_158;
goto block_156;
}
else
{
uint8_t x_159; 
lean_inc(x_2);
x_159 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_140 = x_159;
goto block_156;
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
lean_dec(x_15);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_20, 6);
lean_ctor_set(x_18, 1, x_23);
lean_ctor_set(x_18, 0, x_22);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_11);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_8);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_12);
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
lean_ctor_set(x_45, 1, x_11);
x_46 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_9);
lean_ctor_set(x_46, 2, x_14);
lean_ctor_set(x_46, 3, x_8);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_46, sizeof(void*)*5 + 1, x_12);
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
lean_dec(x_15);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_54, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_54, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_54, 7);
lean_inc(x_65);
x_66 = lean_ctor_get(x_54, 8);
lean_inc(x_66);
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
lean_ctor_set(x_69, 1, x_11);
x_70 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_70, 0, x_13);
lean_ctor_set(x_70, 1, x_9);
lean_ctor_set(x_70, 2, x_14);
lean_ctor_set(x_70, 3, x_8);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_70, sizeof(void*)*5 + 1, x_12);
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
block_106:
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_2, x_5, x_6, x_7);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_80);
x_91 = l_Lean_FileMap_toPosition(x_80, x_83);
lean_dec(x_83);
x_92 = l_Lean_FileMap_toPosition(x_80, x_86);
lean_dec(x_86);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
if (x_82 == 0)
{
lean_free_object(x_87);
lean_dec(x_79);
x_8 = x_94;
x_9 = x_91;
x_10 = x_81;
x_11 = x_89;
x_12 = x_84;
x_13 = x_85;
x_14 = x_93;
x_15 = x_5;
x_16 = x_6;
x_17 = x_90;
goto block_78;
}
else
{
uint8_t x_95; 
lean_inc(x_89);
x_95 = l_Lean_MessageData_hasTag(x_79, x_89);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_85);
lean_dec(x_5);
x_96 = lean_box(0);
lean_ctor_set(x_87, 0, x_96);
return x_87;
}
else
{
lean_free_object(x_87);
x_8 = x_94;
x_9 = x_91;
x_10 = x_81;
x_11 = x_89;
x_12 = x_84;
x_13 = x_85;
x_14 = x_93;
x_15 = x_5;
x_16 = x_6;
x_17 = x_90;
goto block_78;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_87, 0);
x_98 = lean_ctor_get(x_87, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_87);
lean_inc(x_80);
x_99 = l_Lean_FileMap_toPosition(x_80, x_83);
lean_dec(x_83);
x_100 = l_Lean_FileMap_toPosition(x_80, x_86);
lean_dec(x_86);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
if (x_82 == 0)
{
lean_dec(x_79);
x_8 = x_102;
x_9 = x_99;
x_10 = x_81;
x_11 = x_97;
x_12 = x_84;
x_13 = x_85;
x_14 = x_101;
x_15 = x_5;
x_16 = x_6;
x_17 = x_98;
goto block_78;
}
else
{
uint8_t x_103; 
lean_inc(x_97);
x_103 = l_Lean_MessageData_hasTag(x_79, x_97);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_85);
lean_dec(x_5);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_98);
return x_105;
}
else
{
x_8 = x_102;
x_9 = x_99;
x_10 = x_81;
x_11 = x_97;
x_12 = x_84;
x_13 = x_85;
x_14 = x_101;
x_15 = x_5;
x_16 = x_6;
x_17 = x_98;
goto block_78;
}
}
}
}
block_117:
{
lean_object* x_115; 
x_115 = l_Lean_Syntax_getTailPos_x3f(x_113, x_109);
lean_dec(x_113);
if (lean_obj_tag(x_115) == 0)
{
lean_inc(x_114);
x_79 = x_107;
x_80 = x_108;
x_81 = x_109;
x_82 = x_110;
x_83 = x_114;
x_84 = x_111;
x_85 = x_112;
x_86 = x_114;
goto block_106;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec(x_115);
x_79 = x_107;
x_80 = x_108;
x_81 = x_109;
x_82 = x_110;
x_83 = x_114;
x_84 = x_111;
x_85 = x_112;
x_86 = x_116;
goto block_106;
}
}
block_129:
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lean_replaceRef(x_1, x_122);
lean_dec(x_122);
x_126 = l_Lean_Syntax_getPos_x3f(x_125, x_120);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_unsigned_to_nat(0u);
x_107 = x_118;
x_108 = x_119;
x_109 = x_120;
x_110 = x_121;
x_111 = x_124;
x_112 = x_123;
x_113 = x_125;
x_114 = x_127;
goto block_117;
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_107 = x_118;
x_108 = x_119;
x_109 = x_120;
x_110 = x_121;
x_111 = x_124;
x_112 = x_123;
x_113 = x_125;
x_114 = x_128;
goto block_117;
}
}
block_139:
{
if (x_137 == 0)
{
x_118 = x_131;
x_119 = x_132;
x_120 = x_136;
x_121 = x_133;
x_122 = x_134;
x_123 = x_135;
x_124 = x_3;
goto block_129;
}
else
{
uint8_t x_138; 
x_138 = lean_unbox(x_130);
x_118 = x_131;
x_119 = x_132;
x_120 = x_136;
x_121 = x_133;
x_122 = x_134;
x_123 = x_135;
x_124 = x_138;
goto block_129;
}
}
block_156:
{
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_151; 
x_141 = lean_ctor_get(x_5, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_5, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_5, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_5, 5);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_146 = lean_box(x_140);
x_147 = lean_box(x_145);
x_148 = lean_alloc_closure((void*)(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___lam__0___boxed), 3, 2);
lean_closure_set(x_148, 0, x_146);
lean_closure_set(x_148, 1, x_147);
x_149 = lean_box(1);
x_150 = lean_unbox(x_149);
x_151 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_3, x_150);
if (x_151 == 0)
{
lean_dec(x_143);
x_131 = x_148;
x_132 = x_142;
x_133 = x_145;
x_134 = x_144;
x_135 = x_141;
x_136 = x_140;
x_137 = x_151;
goto block_139;
}
else
{
lean_object* x_152; uint8_t x_153; 
x_152 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___closed__0;
x_153 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_143, x_152);
lean_dec(x_143);
x_131 = x_148;
x_132 = x_142;
x_133 = x_145;
x_134 = x_144;
x_135 = x_141;
x_136 = x_140;
x_137 = x_153;
goto block_139;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_5);
lean_dec(x_2);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_7);
return x_155;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 5);
lean_inc(x_7);
x_8 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_box(2);
x_6 = lean_box(0);
x_7 = lean_unbox(x_5);
x_8 = lean_unbox(x_6);
x_9 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23(x_1, x_7, x_8, x_2, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_get_set_stdout(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg___lam__0(x_7, x_9, x_13, x_12);
lean_dec(x_13);
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
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg___lam__0(x_7, x_9, x_21, x_20);
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_get_set_stdin(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg___lam__0(x_7, x_9, x_13, x_12);
lean_dec(x_13);
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
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg___lam__0(x_7, x_9, x_21, x_20);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_get_set_stderr(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg___lam__0(x_7, x_9, x_13, x_12);
lean_dec(x_13);
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
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg___lam__0(x_7, x_9, x_21, x_20);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__0() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__3;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(129u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__0;
x_13 = lean_st_mk_ref(x_12, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_12, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
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
lean_inc(x_20);
x_39 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28), 6, 3);
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
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
block_38:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26), 6, 3);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
x_23 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg(x_19, x_22, x_3, x_4, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_string_validate_utf8(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
x_31 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__4;
x_32 = l_panic___at___Lean_Name_getString_x21_spec__0(x_31);
x_6 = x_24;
x_7 = x_28;
x_8 = x_32;
goto block_11;
}
else
{
lean_object* x_33; 
x_33 = lean_string_from_utf8_unchecked(x_29);
lean_dec(x_29);
x_6 = x_24;
x_7 = x_28;
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg(x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4;
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2;
x_3 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1;
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_20; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_io_get_tid(x_6);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_take(x_5, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_38, 6);
x_42 = lean_ctor_get(x_38, 8);
lean_dec(x_42);
x_43 = lean_ctor_get(x_38, 7);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 4);
lean_dec(x_44);
x_45 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
x_46 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_unbox_uint64(x_35);
lean_dec(x_35);
lean_ctor_set_uint64(x_46, sizeof(void*)*1, x_47);
x_48 = l_Lean_MessageLog_markAllReported(x_41);
x_49 = lean_box(1);
x_50 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5;
x_51 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
lean_ctor_set(x_38, 8, x_51);
lean_ctor_set(x_38, 7, x_50);
lean_ctor_set(x_38, 6, x_48);
lean_ctor_set(x_38, 4, x_46);
x_52 = lean_st_ref_set(x_5, x_38, x_39);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_114_;
x_55 = lean_apply_1(x_1, x_2);
x_56 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_57 = lean_unbox(x_49);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(x_54, x_3, x_55, x_57, x_56, x_4, x_5, x_53);
if (lean_obj_tag(x_58) == 0)
{
x_20 = x_58;
goto block_33;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Exception_isInterrupt(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_Exception_toMessageData(x_59);
lean_inc(x_4);
x_63 = l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23(x_62, x_4, x_5, x_60);
x_20 = x_63;
goto block_33;
}
else
{
lean_dec(x_59);
x_7 = x_60;
goto block_19;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_64 = lean_ctor_get(x_38, 0);
x_65 = lean_ctor_get(x_38, 1);
x_66 = lean_ctor_get(x_38, 2);
x_67 = lean_ctor_get(x_38, 3);
x_68 = lean_ctor_get(x_38, 5);
x_69 = lean_ctor_get(x_38, 6);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_38);
x_70 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2;
x_71 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_unbox_uint64(x_35);
lean_dec(x_35);
lean_ctor_set_uint64(x_71, sizeof(void*)*1, x_72);
x_73 = l_Lean_MessageLog_markAllReported(x_69);
x_74 = lean_box(1);
x_75 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__5;
x_76 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
x_77 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_65);
lean_ctor_set(x_77, 2, x_66);
lean_ctor_set(x_77, 3, x_67);
lean_ctor_set(x_77, 4, x_71);
lean_ctor_set(x_77, 5, x_68);
lean_ctor_set(x_77, 6, x_73);
lean_ctor_set(x_77, 7, x_75);
lean_ctor_set(x_77, 8, x_76);
x_78 = lean_st_ref_set(x_5, x_77, x_39);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_114_;
x_81 = lean_apply_1(x_1, x_2);
x_82 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_83 = lean_unbox(x_74);
lean_inc(x_5);
lean_inc(x_4);
x_84 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(x_80, x_3, x_81, x_83, x_82, x_4, x_5, x_79);
if (lean_obj_tag(x_84) == 0)
{
x_20 = x_84;
goto block_33;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Exception_isInterrupt(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_Exception_toMessageData(x_85);
lean_inc(x_4);
x_89 = l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23(x_88, x_4, x_5, x_86);
x_20 = x_89;
goto block_33;
}
else
{
lean_dec(x_85);
x_7 = x_86;
goto block_19;
}
}
}
block_19:
{
lean_object* x_8; 
lean_inc(x_5);
x_8 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(x_4, x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
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
else
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
block_33:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_7 = x_21;
goto block_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(x_4, x_5, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_22);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
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
x_10 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_7, x_9);
lean_dec(x_7);
x_11 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg(x_8, x_10, x_4, x_5, x_6);
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
x_2 = lean_box(0);
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
x_1 = lean_box(0);
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
x_2 = lean_box(0);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__9;
x_3 = lean_box(0);
x_4 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__5;
x_5 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
x_7 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
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
lean_dec(x_6);
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
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed), 5, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2), 6, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_inc(x_4);
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
lean_dec(x_2);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(x_1, x_2, x_13, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__11(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___lam__0(x_1, x_5, x_6, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13(x_1, x_2, x_11, x_4, x_12, x_13, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__18(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__21(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__26___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__27___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26_spec__28___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_19 = lean_ctor_get(x_4, 11);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_21 = lean_ctor_get(x_4, 12);
lean_inc(x_21);
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
lean_dec(x_3);
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
lean_dec(x_3);
x_8 = lean_apply_2(x_1, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
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
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
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
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
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
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_4);
x_9 = lean_apply_2(x_1, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
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
x_1 = lean_alloc_closure((void*)(l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_30____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
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
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
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
lean_dec(x_3);
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
x_10 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_80_;
x_11 = lean_string_dec_eq(x_6, x_10);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Expr_forallE___override(x_8, x_1, x_2, x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Expr_forallE___override(x_12, x_1, x_2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
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
lean_dec(x_3);
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
lean_dec(x_11);
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
lean_dec(x_1);
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
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrowN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkArrowN(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_4; uint8_t x_14; uint8_t x_16; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_is_aux_recursor(x_2, x_4);
if (x_16 == 0)
{
x_14 = x_16;
goto block_15;
}
else
{
uint8_t x_17; 
lean_inc(x_4);
lean_inc(x_2);
x_17 = l_Lean_isCasesOnRecursor(x_2, x_4);
if (x_17 == 0)
{
x_14 = x_16;
goto block_15;
}
else
{
goto block_13;
}
}
block_11:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_6 = l_Array_contains___redArg(x_1, x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
block_13:
{
uint8_t x_12; 
lean_inc(x_4);
x_12 = l_Lean_isRecCore(x_2, x_4);
if (x_12 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
else
{
goto block_11;
}
}
block_15:
{
if (x_14 == 0)
{
goto block_13;
}
else
{
lean_dec(x_2);
goto block_11;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
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
lean_dec(x_4);
lean_dec(x_3);
goto block_9;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
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
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_3);
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
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5857_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5857_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("enableNew", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5857_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5857_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5857_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5857_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(compiler) enable the new code generator, unset to use the old code generator instead", 85, 85);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5857_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5857_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5857_;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5857_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5857_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5857_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5857_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5857_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5857_;
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5857_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
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
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_io_get_task_state(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_task_get_own(x_2);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_task_get_own(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__0___boxed), 5, 1);
lean_closure_set(x_15, 0, x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_16, 0, x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__2), 4, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_traceBlock___redArg___closed__1;
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(x_18, x_15, x_17, x_20, x_1, x_3, x_4, x_14);
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
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_profileitM___at___Lean_traceBlock_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_traceBlock___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_traceBlock___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDeclsNew___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_lcnf_compile_decls(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDeclsOld___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_compile_decls(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofName(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofName(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_apply_5(x_1, x_2, x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_2 = x_12;
x_3 = x_9;
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_4);
x_18 = lean_apply_5(x_1, x_2, x_17, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_4);
x_21 = lean_apply_5(x_1, x_19, x_16, x_4, x_5, x_20);
x_10 = x_21;
goto block_14;
}
else
{
lean_dec(x_16);
x_10 = x_18;
goto block_14;
}
block_14:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_2 = x_11;
x_3 = x_9;
x_6 = x_12;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 2);
lean_inc(x_16);
lean_dec(x_8);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_4);
x_17 = lean_apply_5(x_1, x_2, x_15, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_20 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1(x_1, x_18, x_16, x_4, x_5, x_19);
x_10 = x_20;
goto block_14;
}
else
{
lean_dec(x_16);
x_10 = x_17;
goto block_14;
}
block_14:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_2 = x_11;
x_3 = x_9;
x_6 = x_12;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_10; 
x_10 = lean_find_expr(x_1, x_3);
if (lean_obj_tag(x_10) == 0)
{
goto block_9;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1;
x_14 = l_Lean_MessageData_ofName(x_12);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_17, x_4, x_5, x_6);
return x_18;
}
else
{
lean_dec(x_11);
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0(x_1, x_3, x_10, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
case 4:
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(x_7, x_3, x_13, x_4, x_5, x_6);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__3(x_7, x_3, x_15, x_4, x_5, x_6);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0(x_1, x_3, x_20, x_4, x_5, x_6);
lean_dec(x_20);
lean_dec(x_3);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0(x_1, x_22, x_19, x_4, x_5, x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_22);
lean_dec(x_1);
return x_24;
}
else
{
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_21;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; uint8_t x_13; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_15 = lean_is_aux_recursor(x_1, x_3);
if (x_15 == 0)
{
x_13 = x_15;
goto block_14;
}
else
{
uint8_t x_16; 
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_isCasesOnRecursor(x_1, x_3);
if (x_16 == 0)
{
x_13 = x_15;
goto block_14;
}
else
{
goto block_12;
}
}
block_10:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_5 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_4, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
block_12:
{
uint8_t x_11; 
lean_inc(x_3);
x_11 = l_Lean_isRecCore(x_1, x_3);
if (x_11 == 0)
{
lean_dec(x_3);
return x_11;
}
else
{
goto block_10;
}
}
block_14:
{
if (x_13 == 0)
{
goto block_12;
}
else
{
lean_dec(x_1);
goto block_10;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1(x_9, x_1, x_10, x_2, x_3, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l_Lean_Kernel_Exception_toMessageData(x_1, x_6);
x_8 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_7, x_3, x_4, x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 16)
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(x_4);
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
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg___lam__0(x_1, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_dec(x_7);
x_10 = lean_st_ref_take(x_3, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 5);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Environment_setExporting(x_14, x_17);
x_19 = l_Lean_Core_instInhabitedCache___closed__2;
lean_ctor_set(x_11, 5, x_19);
lean_ctor_set(x_11, 0, x_18);
x_20 = lean_st_ref_set(x_3, x_11, x_12);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_3);
x_22 = lean_apply_3(x_1, x_2, x_3, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(x_3, x_9, x_19, x_25, x_24);
lean_dec(x_25);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_23);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_box(0);
x_34 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(x_3, x_9, x_19, x_33, x_32);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_31);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
x_41 = lean_ctor_get(x_11, 2);
x_42 = lean_ctor_get(x_11, 3);
x_43 = lean_ctor_get(x_11, 4);
x_44 = lean_ctor_get(x_11, 6);
x_45 = lean_ctor_get(x_11, 7);
x_46 = lean_ctor_get(x_11, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
x_49 = l_Lean_Environment_setExporting(x_39, x_48);
x_50 = l_Lean_Core_instInhabitedCache___closed__2;
x_51 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_42);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set(x_51, 6, x_44);
lean_ctor_set(x_51, 7, x_45);
lean_ctor_set(x_51, 8, x_46);
x_52 = lean_st_ref_set(x_3, x_51, x_12);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
lean_inc(x_3);
x_54 = lean_apply_3(x_1, x_2, x_3, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_55);
x_58 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(x_3, x_9, x_50, x_57, x_56);
lean_dec(x_57);
lean_dec(x_3);
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
lean_dec(x_54);
x_64 = lean_box(0);
x_65 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(x_3, x_9, x_50, x_64, x_63);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_compileDecls_doCompile___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0___redArg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_compileDecls_doCompile___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiling old: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_compileDecls_doCompile___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_compileDecls_doCompile___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_compileDecls_doCompile___lam__1___closed__1;
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_1, x_7);
x_9 = l_Lean_MessageData_ofList(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Core_instantiateValueLevelParams___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_compile_decls(x_9, x_1, x_2);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_compile_decls(x_13, x_1, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_lcnf_compile_decls(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
return x_6;
}
else
{
if (x_2 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
return x_6;
}
}
}
}
static lean_object* _init_l_Lean_compileDecls_doCompile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_compiler_enableNew;
return x_1;
}
}
static lean_object* _init_l_Lean_compileDecls_doCompile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5857_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Environment_constants(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
lean_inc(x_1);
x_14 = l_List_all___redArg(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_7);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = l_Lean_compileDecls_doCompile___closed__0;
x_18 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__1___boxed), 5, 1);
lean_closure_set(x_19, 0, x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__2___boxed), 5, 2);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_1);
x_21 = l_Lean_compileDecls_doCompile___closed__1;
x_22 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(x_21, x_19, x_20, x_14, x_22, x_4, x_5, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 12)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_30 = x_25;
} else {
 lean_dec_ref(x_25);
 x_30 = lean_box(0);
}
if (x_3 == 0)
{
lean_object* x_38; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_38 = lean_box(0);
lean_ctor_set(x_23, 0, x_38);
return x_23;
}
else
{
lean_free_object(x_23);
if (lean_obj_tag(x_2) == 0)
{
x_31 = x_4;
x_32 = x_5;
x_33 = x_27;
goto block_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(x_39, x_4, x_5, x_27);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_31 = x_4;
x_32 = x_5;
x_33 = x_41;
goto block_37;
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
return x_40;
}
}
}
block_37:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(3, 1, 0);
} else {
 x_34 = x_30;
 lean_ctor_set_tag(x_34, 3);
}
lean_ctor_set(x_34, 0, x_29);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_35, x_31, x_32, x_33);
lean_dec(x_32);
lean_dec(x_31);
return x_36;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
if (x_3 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_42);
return x_53;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
x_45 = x_4;
x_46 = x_5;
x_47 = x_42;
goto block_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_55 = l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(x_54, x_4, x_5, x_42);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_45 = x_4;
x_46 = x_5;
x_47 = x_56;
goto block_51;
}
else
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
return x_55;
}
}
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_44)) {
 x_48 = lean_alloc_ctor(3, 1, 0);
} else {
 x_48 = x_44;
 lean_ctor_set_tag(x_48, 3);
}
lean_ctor_set(x_48, 0, x_43);
x_49 = l_Lean_MessageData_ofFormat(x_48);
x_50 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_49, x_45, x_46, x_47);
lean_dec(x_46);
lean_dec(x_45);
return x_50;
}
}
}
else
{
lean_dec(x_2);
if (x_3 == 0)
{
uint8_t x_57; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_23);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_23, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_23, 0, x_59);
return x_23;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_23, 1);
lean_inc(x_60);
lean_dec(x_23);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_23, 1);
lean_inc(x_63);
lean_dec(x_23);
x_64 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg(x_25, x_4, x_5, x_63);
lean_dec(x_5);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_4);
lean_dec(x_2);
x_65 = lean_ctor_get(x_23, 1);
lean_inc(x_65);
lean_dec(x_23);
x_66 = lean_ctor_get(x_24, 0);
lean_inc(x_66);
lean_dec(x_24);
x_67 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(x_66, x_5, x_65);
lean_dec(x_5);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_23);
if (x_68 == 0)
{
return x_23;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_23, 0);
x_70 = lean_ctor_get(x_23, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_23);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_16);
lean_dec(x_2);
x_72 = lean_box(x_3);
x_73 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__3___boxed), 5, 2);
lean_closure_set(x_73, 0, x_1);
lean_closure_set(x_73, 1, x_72);
x_74 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg(x_73, x_4, x_5, x_10);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_7, 0);
x_76 = lean_ctor_get(x_7, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_7);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Environment_constants(x_77);
x_79 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__0___boxed), 2, 1);
lean_closure_set(x_79, 0, x_78);
lean_inc(x_1);
x_80 = l_List_all___redArg(x_1, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_4, 2);
lean_inc(x_83);
x_84 = l_Lean_compileDecls_doCompile___closed__0;
x_85 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_inc(x_1);
x_86 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__1___boxed), 5, 1);
lean_closure_set(x_86, 0, x_1);
x_87 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__2___boxed), 5, 2);
lean_closure_set(x_87, 0, x_83);
lean_closure_set(x_87, 1, x_1);
x_88 = l_Lean_compileDecls_doCompile___closed__1;
x_89 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
lean_inc(x_5);
lean_inc(x_4);
x_90 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(x_88, x_86, x_87, x_80, x_89, x_4, x_5, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
if (lean_obj_tag(x_92) == 12)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
 x_96 = lean_box(0);
}
if (x_3 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_104 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_94;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_93);
return x_105;
}
else
{
lean_dec(x_94);
if (lean_obj_tag(x_2) == 0)
{
x_97 = x_4;
x_98 = x_5;
x_99 = x_93;
goto block_103;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_2, 0);
lean_inc(x_106);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_107 = l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(x_106, x_4, x_5, x_93);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_97 = x_4;
x_98 = x_5;
x_99 = x_108;
goto block_103;
}
else
{
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_5);
lean_dec(x_4);
return x_107;
}
}
}
block_103:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(3, 1, 0);
} else {
 x_100 = x_96;
 lean_ctor_set_tag(x_100, 3);
}
lean_ctor_set(x_100, 0, x_95);
x_101 = l_Lean_MessageData_ofFormat(x_100);
x_102 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_101, x_97, x_98, x_99);
lean_dec(x_98);
lean_dec(x_97);
return x_102;
}
}
else
{
lean_dec(x_2);
if (x_3 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_92);
lean_dec(x_5);
lean_dec(x_4);
x_109 = lean_ctor_get(x_90, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_110 = x_90;
} else {
 lean_dec_ref(x_90);
 x_110 = lean_box(0);
}
x_111 = lean_box(0);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_90, 1);
lean_inc(x_113);
lean_dec(x_90);
x_114 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg(x_92, x_4, x_5, x_113);
lean_dec(x_5);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_4);
lean_dec(x_2);
x_115 = lean_ctor_get(x_90, 1);
lean_inc(x_115);
lean_dec(x_90);
x_116 = lean_ctor_get(x_91, 0);
lean_inc(x_116);
lean_dec(x_91);
x_117 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(x_116, x_5, x_115);
lean_dec(x_5);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_118 = lean_ctor_get(x_90, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_90, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_120 = x_90;
} else {
 lean_dec_ref(x_90);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_83);
lean_dec(x_2);
x_122 = lean_box(x_3);
x_123 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__3___boxed), 5, 2);
lean_closure_set(x_123, 0, x_1);
lean_closure_set(x_123, 1, x_122);
x_124 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg(x_123, x_4, x_5, x_76);
return x_124;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_compileDecls_doCompile___lam__0(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_compileDecls_doCompile___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_compileDecls_doCompile___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_compileDecls_doCompile___lam__3(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_compileDecls_doCompile(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
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
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(x_1, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
x_12 = l_Lean_compileDecls_doCompile(x_3, x_4, x_5, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Lean_compileDecls___lam__1(x_8, x_2, x_15, x_14);
lean_dec(x_15);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = l_Lean_compileDecls___lam__1(x_8, x_2, x_23, x_22);
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
return x_28;
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
x_2 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_30 = lean_ctor_get(x_4, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_4, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec(x_8);
x_33 = l_Lean_compileDecls___closed__1;
x_34 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_30, x_33);
lean_dec(x_30);
if (x_34 == 0)
{
lean_dec(x_32);
lean_dec(x_31);
goto block_29;
}
else
{
uint8_t x_35; 
x_35 = l_Lean_Environment_isRealizing(x_32);
lean_dec(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_36 = lean_st_ref_get(x_5, x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_39);
x_40 = l_Lean_Environment_promiseChecked(x_39, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(x_43, x_5, x_42);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_IO_CancelToken_new(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(x_35);
x_51 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__2___boxed), 2, 1);
lean_closure_set(x_51, 0, x_50);
x_52 = lean_box(x_3);
x_53 = lean_alloc_closure((void*)(l_Lean_compileDecls___lam__0___boxed), 9, 5);
lean_closure_set(x_53, 0, x_44);
lean_closure_set(x_53, 1, x_41);
lean_closure_set(x_53, 2, x_1);
lean_closure_set(x_53, 3, x_2);
lean_closure_set(x_53, 4, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_48);
x_55 = l_Lean_compileDecls___closed__3;
x_56 = l_Lean_Name_toString(x_55, x_34, x_51);
lean_inc(x_54);
x_57 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_53, x_54, x_56, x_4, x_5, x_49);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_39, 2);
lean_inc(x_60);
lean_dec(x_39);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_io_map_task(x_58, x_60, x_61, x_35, x_59);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_71; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_71 = l_Lean_Syntax_getTailPos_x3f(x_31, x_35);
lean_dec(x_31);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_free_object(x_62);
x_72 = lean_box(0);
x_66 = x_72;
goto block_70;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_ctor_set(x_62, 1, x_74);
lean_ctor_set(x_62, 0, x_74);
lean_ctor_set(x_71, 0, x_62);
x_66 = x_71;
goto block_70;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
lean_dec(x_71);
lean_inc(x_75);
lean_ctor_set(x_62, 1, x_75);
lean_ctor_set(x_62, 0, x_75);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_62);
x_66 = x_76;
goto block_70;
}
}
block_70:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_54);
lean_ctor_set(x_68, 3, x_64);
x_69 = l_Lean_Core_logSnapshotTask___redArg(x_68, x_5, x_65);
lean_dec(x_5);
return x_69;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_84; 
x_77 = lean_ctor_get(x_62, 0);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_62);
x_84 = l_Lean_Syntax_getTailPos_x3f(x_31, x_35);
lean_dec(x_31);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_box(0);
x_79 = x_85;
goto block_83;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
lean_inc(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_86);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
x_79 = x_89;
goto block_83;
}
block_83:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_54);
lean_ctor_set(x_81, 3, x_77);
x_82 = l_Lean_Core_logSnapshotTask___redArg(x_81, x_5, x_78);
lean_dec(x_5);
return x_82;
}
}
}
else
{
lean_dec(x_31);
goto block_29;
}
}
block_29:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_compileDecls___closed__0;
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_traceBlock___redArg(x_15, x_14, x_4, x_5, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_compileDecls_doCompile(x_1, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
return x_18;
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_compileDecls___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_compileDecls___lam__0(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_compileDecls(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_6 = l_Lean_Compiler_getDeclNamesForCodeGen(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lean_compileDecls(x_6, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_compileDecl(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_getDiag(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_3 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_1, x_2);
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
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isDiagnosticsEnabled(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_1 = lean_box(0);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__4;
x_2 = l_Lean_ImportM_runCoreM___redArg___closed__9;
x_3 = l_Lean_ImportM_runCoreM___redArg___closed__8;
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
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
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_;
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
x_1 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; uint8_t x_182; 
x_4 = lean_io_get_num_heartbeats(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
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
lean_inc(x_7);
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
lean_dec(x_21);
x_127 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___closed__0;
x_128 = lean_st_ref_get(x_127, x_23);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_st_ref_get(x_22, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_ImportM_runCoreM___redArg___closed__11;
x_136 = l_Lean_ImportM_runCoreM___redArg___closed__13;
x_137 = lean_box(0);
x_138 = lean_box(0);
x_139 = lean_box(0);
x_140 = l_Lean_ImportM_runCoreM___redArg___closed__14;
x_141 = lean_box(0);
x_142 = lean_box(0);
x_143 = l_Lean_useDiagnosticMsg___lam__3___closed__0;
x_144 = l_Lean_ImportM_runCoreM___redArg___closed__15;
x_182 = l_Lean_Kernel_isDiagnosticsEnabled(x_134);
lean_dec(x_134);
if (x_182 == 0)
{
if (x_144 == 0)
{
lean_inc(x_22);
x_145 = x_22;
x_146 = x_133;
goto block_159;
}
else
{
goto block_181;
}
}
else
{
if (x_144 == 0)
{
goto block_181;
}
else
{
lean_inc(x_22);
x_145 = x_22;
x_146 = x_133;
goto block_159;
}
}
block_75:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_8, x_25);
lean_dec(x_25);
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
lean_ctor_set_uint8(x_41, sizeof(void*)*13, x_24);
lean_ctor_set_uint8(x_41, sizeof(void*)*13 + 1, x_36);
x_42 = lean_apply_3(x_1, x_41, x_38, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
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
lean_dec(x_42);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
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
lean_dec(x_50);
x_64 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_65 = l_Nat_reprFast(x_63);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
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
lean_dec(x_50);
x_70 = l_Lean_Core_CoreM_toIO___redArg___closed__0;
x_71 = l_Nat_reprFast(x_69);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
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
block_126:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_st_ref_take(x_77, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 5);
lean_dec(x_86);
x_87 = l_Lean_Kernel_enableDiag(x_85, x_76);
lean_ctor_set(x_82, 5, x_16);
lean_ctor_set(x_82, 0, x_87);
x_88 = lean_st_ref_set(x_77, x_82, x_83);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get(x_78, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_78, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_78, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_78, 5);
lean_inc(x_93);
x_94 = lean_ctor_get(x_78, 6);
lean_inc(x_94);
x_95 = lean_ctor_get(x_78, 7);
lean_inc(x_95);
x_96 = lean_ctor_get(x_78, 8);
lean_inc(x_96);
x_97 = lean_ctor_get(x_78, 9);
lean_inc(x_97);
x_98 = lean_ctor_get(x_78, 10);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 11);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_78, sizeof(void*)*13 + 1);
x_101 = lean_ctor_get(x_78, 12);
lean_inc(x_101);
lean_dec(x_78);
x_24 = x_76;
x_25 = x_79;
x_26 = x_90;
x_27 = x_91;
x_28 = x_92;
x_29 = x_93;
x_30 = x_94;
x_31 = x_95;
x_32 = x_96;
x_33 = x_97;
x_34 = x_98;
x_35 = x_99;
x_36 = x_100;
x_37 = x_101;
x_38 = x_77;
x_39 = x_89;
goto block_75;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
x_102 = lean_ctor_get(x_82, 0);
x_103 = lean_ctor_get(x_82, 1);
x_104 = lean_ctor_get(x_82, 2);
x_105 = lean_ctor_get(x_82, 3);
x_106 = lean_ctor_get(x_82, 4);
x_107 = lean_ctor_get(x_82, 6);
x_108 = lean_ctor_get(x_82, 7);
x_109 = lean_ctor_get(x_82, 8);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_82);
x_110 = l_Lean_Kernel_enableDiag(x_102, x_76);
x_111 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_103);
lean_ctor_set(x_111, 2, x_104);
lean_ctor_set(x_111, 3, x_105);
lean_ctor_set(x_111, 4, x_106);
lean_ctor_set(x_111, 5, x_16);
lean_ctor_set(x_111, 6, x_107);
lean_ctor_set(x_111, 7, x_108);
lean_ctor_set(x_111, 8, x_109);
x_112 = lean_st_ref_set(x_77, x_111, x_83);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_ctor_get(x_78, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_78, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_78, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_78, 5);
lean_inc(x_117);
x_118 = lean_ctor_get(x_78, 6);
lean_inc(x_118);
x_119 = lean_ctor_get(x_78, 7);
lean_inc(x_119);
x_120 = lean_ctor_get(x_78, 8);
lean_inc(x_120);
x_121 = lean_ctor_get(x_78, 9);
lean_inc(x_121);
x_122 = lean_ctor_get(x_78, 10);
lean_inc(x_122);
x_123 = lean_ctor_get(x_78, 11);
lean_inc(x_123);
x_124 = lean_ctor_get_uint8(x_78, sizeof(void*)*13 + 1);
x_125 = lean_ctor_get(x_78, 12);
lean_inc(x_125);
lean_dec(x_78);
x_24 = x_76;
x_25 = x_79;
x_26 = x_114;
x_27 = x_115;
x_28 = x_116;
x_29 = x_117;
x_30 = x_118;
x_31 = x_119;
x_32 = x_120;
x_33 = x_121;
x_34 = x_122;
x_35 = x_123;
x_36 = x_124;
x_37 = x_125;
x_38 = x_77;
x_39 = x_113;
goto block_75;
}
}
block_159:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; 
x_147 = lean_st_ref_get(x_145, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0___closed__0;
x_152 = l_Lean_ImportM_runCoreM___redArg___closed__16;
lean_inc(x_129);
lean_inc(x_5);
x_153 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_153, 0, x_135);
lean_ctor_set(x_153, 1, x_136);
lean_ctor_set(x_153, 2, x_137);
lean_ctor_set(x_153, 3, x_9);
lean_ctor_set(x_153, 4, x_152);
lean_ctor_set(x_153, 5, x_138);
lean_ctor_set(x_153, 6, x_10);
lean_ctor_set(x_153, 7, x_139);
lean_ctor_set(x_153, 8, x_5);
lean_ctor_set(x_153, 9, x_140);
lean_ctor_set(x_153, 10, x_11);
lean_ctor_set(x_153, 11, x_142);
lean_ctor_set(x_153, 12, x_129);
lean_ctor_set_uint8(x_153, sizeof(void*)*13, x_144);
x_154 = lean_unbox(x_141);
lean_ctor_set_uint8(x_153, sizeof(void*)*13 + 1, x_154);
x_155 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_8, x_143);
x_156 = l_Lean_Kernel_isDiagnosticsEnabled(x_150);
lean_dec(x_150);
if (x_156 == 0)
{
if (x_155 == 0)
{
uint8_t x_157; 
lean_dec(x_153);
x_157 = lean_unbox(x_141);
x_24 = x_155;
x_25 = x_151;
x_26 = x_135;
x_27 = x_136;
x_28 = x_9;
x_29 = x_138;
x_30 = x_10;
x_31 = x_139;
x_32 = x_5;
x_33 = x_140;
x_34 = x_11;
x_35 = x_142;
x_36 = x_157;
x_37 = x_129;
x_38 = x_145;
x_39 = x_149;
goto block_75;
}
else
{
lean_dec(x_129);
lean_dec(x_5);
x_76 = x_155;
x_77 = x_145;
x_78 = x_153;
x_79 = x_151;
x_80 = x_149;
goto block_126;
}
}
else
{
if (x_155 == 0)
{
lean_dec(x_129);
lean_dec(x_5);
x_76 = x_155;
x_77 = x_145;
x_78 = x_153;
x_79 = x_151;
x_80 = x_149;
goto block_126;
}
else
{
uint8_t x_158; 
lean_dec(x_153);
x_158 = lean_unbox(x_141);
x_24 = x_155;
x_25 = x_151;
x_26 = x_135;
x_27 = x_136;
x_28 = x_9;
x_29 = x_138;
x_30 = x_10;
x_31 = x_139;
x_32 = x_5;
x_33 = x_140;
x_34 = x_11;
x_35 = x_142;
x_36 = x_158;
x_37 = x_129;
x_38 = x_145;
x_39 = x_149;
goto block_75;
}
}
}
block_181:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_160 = lean_st_ref_take(x_22, x_133);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = !lean_is_exclusive(x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_161, 0);
x_165 = lean_ctor_get(x_161, 5);
lean_dec(x_165);
x_166 = l_Lean_Kernel_enableDiag(x_164, x_144);
lean_ctor_set(x_161, 5, x_16);
lean_ctor_set(x_161, 0, x_166);
x_167 = lean_st_ref_set(x_22, x_161, x_162);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
lean_inc(x_22);
x_145 = x_22;
x_146 = x_168;
goto block_159;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_169 = lean_ctor_get(x_161, 0);
x_170 = lean_ctor_get(x_161, 1);
x_171 = lean_ctor_get(x_161, 2);
x_172 = lean_ctor_get(x_161, 3);
x_173 = lean_ctor_get(x_161, 4);
x_174 = lean_ctor_get(x_161, 6);
x_175 = lean_ctor_get(x_161, 7);
x_176 = lean_ctor_get(x_161, 8);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_161);
x_177 = l_Lean_Kernel_enableDiag(x_169, x_144);
x_178 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_170);
lean_ctor_set(x_178, 2, x_171);
lean_ctor_set(x_178, 3, x_172);
lean_ctor_set(x_178, 4, x_173);
lean_ctor_set(x_178, 5, x_16);
lean_ctor_set(x_178, 6, x_174);
lean_ctor_set(x_178, 7, x_175);
lean_ctor_set(x_178, 8, x_176);
x_179 = lean_st_ref_set(x_22, x_178, x_162);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
lean_inc(x_22);
x_145 = x_22;
x_146 = x_180;
goto block_159;
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
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ImportM_runCoreM(x_1, x_2, x_3, x_4);
lean_dec(x_3);
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
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_6);
x_10 = lean_apply_4(x_2, x_7, x_3, x_4, x_8);
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_4);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_7);
x_11 = lean_apply_4(x_3, x_8, x_4, x_5, x_9);
return x_11;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_6);
x_10 = lean_apply_4(x_2, x_7, x_3, x_4, x_8);
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_4);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_7);
x_11 = lean_apply_4(x_3, x_8, x_4, x_5, x_9);
return x_11;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
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
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
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
lean_inc(x_6);
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
lean_dec(x_6);
x_11 = l_Lean_NameSet_contains(x_10, x_1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_free_object(x_4);
x_12 = lean_st_ref_take(x_2, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
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
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(1);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_30 = lean_ctor_get(x_14, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_31 = l_Lean_NameSet_insert(x_30, x_1);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_13, 6, x_32);
x_33 = lean_st_ref_set(x_2, x_13, x_15);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(1);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
x_40 = lean_ctor_get(x_13, 2);
x_41 = lean_ctor_get(x_13, 3);
x_42 = lean_ctor_get(x_13, 4);
x_43 = lean_ctor_get(x_13, 5);
x_44 = lean_ctor_get(x_13, 7);
x_45 = lean_ctor_get(x_13, 8);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_46 = lean_ctor_get(x_14, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_14, 2);
lean_inc(x_48);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_49 = x_14;
} else {
 lean_dec_ref(x_14);
 x_49 = lean_box(0);
}
x_50 = l_Lean_NameSet_insert(x_48, x_1);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 3, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_39);
lean_ctor_set(x_52, 2, x_40);
lean_ctor_set(x_52, 3, x_41);
lean_ctor_set(x_52, 4, x_42);
lean_ctor_set(x_52, 5, x_43);
lean_ctor_set(x_52, 6, x_51);
lean_ctor_set(x_52, 7, x_44);
lean_ctor_set(x_52, 8, x_45);
x_53 = lean_st_ref_set(x_2, x_52, x_15);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(1);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_4, 0, x_58);
return x_4;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
lean_dec(x_4);
x_60 = lean_ctor_get(x_6, 2);
lean_inc(x_60);
lean_dec(x_6);
x_61 = l_Lean_NameSet_contains(x_60, x_1);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_62 = lean_st_ref_take(x_2, x_59);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_63, 7);
lean_inc(x_72);
x_73 = lean_ctor_get(x_63, 8);
lean_inc(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 lean_ctor_release(x_63, 5);
 lean_ctor_release(x_63, 6);
 lean_ctor_release(x_63, 7);
 lean_ctor_release(x_63, 8);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_64, 2);
lean_inc(x_77);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 x_78 = x_64;
} else {
 lean_dec_ref(x_64);
 x_78 = lean_box(0);
}
x_79 = l_Lean_NameSet_insert(x_77, x_1);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 3, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_79);
if (lean_is_scalar(x_74)) {
 x_81 = lean_alloc_ctor(0, 9, 0);
} else {
 x_81 = x_74;
}
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_67);
lean_ctor_set(x_81, 2, x_68);
lean_ctor_set(x_81, 3, x_69);
lean_ctor_set(x_81, 4, x_70);
lean_ctor_set(x_81, 5, x_71);
lean_ctor_set(x_81, 6, x_80);
lean_ctor_set(x_81, 7, x_72);
lean_ctor_set(x_81, 8, x_73);
x_82 = lean_st_ref_set(x_2, x_81, x_65);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_85 = lean_box(1);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_59);
return x_88;
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
lean_dec(x_2);
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
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Environment_enableRealizationsForConst(x_8, x_9, x_1, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(x_11, x_3, x_12);
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
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7566_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_912_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7566_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7566_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7566_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7566_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7566_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7566_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7566_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_912_;
x_2 = l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7566_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7566_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7566u);
x_2 = l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7566_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_7566_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_114_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7566_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_traceBlock___redArg___closed__1;
x_9 = lean_unbox(x_3);
x_10 = l_Lean_registerTraceClass(x_8, x_9, x_4, x_7);
return x_10;
}
else
{
return x_6;
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
l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_40_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_40_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_40_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_40_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_40_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_40_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_40_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_40_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_40_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_40_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_40_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_40_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_40_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_40_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_40_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_40_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics_threshold);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_80_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_80_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_80_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_80_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_80_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_80_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_80_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_80_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_80_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_80_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_80_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_80_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_80_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_80_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_80_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_80_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_80_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_maxHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_maxHeartbeats);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_114_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_114_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_114_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_114_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_114_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_114_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_114_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_114_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_114_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_114_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_114_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_114_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_114_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_114_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_114_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_114_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_114_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_async = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_async);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_153_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_153_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_153_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_153_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_153_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_153_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_153_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_153_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_153_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_153_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_153_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_153_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_153_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_153_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_153_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_153_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_inServer = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_inServer);
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_192_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_192_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_192_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_192_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_192_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_192_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_192_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_192_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_192_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_192_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_192_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_192_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_192_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_192_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_192_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_192_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_192_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_192_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_192_(lean_io_mk_world());
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
l_Lean_useDiagnosticMsg___lam__3___closed__0 = _init_l_Lean_useDiagnosticMsg___lam__3___closed__0();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__3___closed__0);
l_Lean_useDiagnosticMsg___lam__3___closed__1 = _init_l_Lean_useDiagnosticMsg___lam__3___closed__1();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__3___closed__1);
l_Lean_useDiagnosticMsg___lam__3___closed__2 = _init_l_Lean_useDiagnosticMsg___lam__3___closed__2();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__3___closed__2);
l_Lean_useDiagnosticMsg___lam__3___closed__3 = _init_l_Lean_useDiagnosticMsg___lam__3___closed__3();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__3___closed__3);
l_Lean_useDiagnosticMsg___lam__3___closed__4 = _init_l_Lean_useDiagnosticMsg___lam__3___closed__4();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__3___closed__4);
l_Lean_useDiagnosticMsg = _init_l_Lean_useDiagnosticMsg();
lean_mark_persistent(l_Lean_useDiagnosticMsg);
l_Lean_instInhabitedDeclNameGenerator___closed__0 = _init_l_Lean_instInhabitedDeclNameGenerator___closed__0();
lean_mark_persistent(l_Lean_instInhabitedDeclNameGenerator___closed__0);
l_Lean_instInhabitedDeclNameGenerator = _init_l_Lean_instInhabitedDeclNameGenerator();
lean_mark_persistent(l_Lean_instInhabitedDeclNameGenerator);
l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__6____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__7____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__8____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__9____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__10____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__11____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__12____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__13____x40_Lean_CoreM___hyg_912_);
l_Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_912_ = _init_l_Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_912_();
lean_mark_persistent(l_Lean_Core_initFn___closed__14____x40_Lean_CoreM___hyg_912_);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_912_(lean_io_mk_world());
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
l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3750_ = _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3750_();
lean_mark_persistent(l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_3750_);
l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3750_ = _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3750_();
lean_mark_persistent(l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_3750_);
l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3750_ = _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3750_();
lean_mark_persistent(l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_3750_);
l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3750_ = _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3750_();
lean_mark_persistent(l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_3750_);
l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3750_ = _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3750_();
lean_mark_persistent(l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_3750_);
l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3750_ = _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3750_();
lean_mark_persistent(l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_3750_);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3750_(lean_io_mk_world());
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
l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4776_ = _init_l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4776_();
lean_mark_persistent(l_Lean_Core_initFn___closed__0____x40_Lean_CoreM___hyg_4776_);
l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4776_ = _init_l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4776_();
lean_mark_persistent(l_Lean_Core_initFn___closed__1____x40_Lean_CoreM___hyg_4776_);
l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4776_ = _init_l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4776_();
lean_mark_persistent(l_Lean_Core_initFn___closed__2____x40_Lean_CoreM___hyg_4776_);
l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4776_ = _init_l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4776_();
lean_mark_persistent(l_Lean_Core_initFn___closed__3____x40_Lean_CoreM___hyg_4776_);
l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4776_ = _init_l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4776_();
lean_mark_persistent(l_Lean_Core_initFn___closed__4____x40_Lean_CoreM___hyg_4776_);
l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4776_ = _init_l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4776_();
lean_mark_persistent(l_Lean_Core_initFn___closed__5____x40_Lean_CoreM___hyg_4776_);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_4776_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_stderrAsMessages = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_stderrAsMessages);
lean_dec_ref(res);
}l___auto___closed__0____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__0____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__0____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__1____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__1____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__1____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__2____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__2____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__2____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__3____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__3____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__3____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__4____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__4____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__4____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__5____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__5____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__5____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__6____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__6____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__6____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__7____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__7____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__7____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__8____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__8____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__8____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__9____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__9____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__9____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__10____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__10____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__10____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__11____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__11____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__11____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__12____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__12____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__12____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__13____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__13____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__13____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__14____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__14____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__14____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__15____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__15____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__15____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__16____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__16____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__16____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__17____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__17____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__17____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__18____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__18____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__18____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__19____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__19____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__19____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__20____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__20____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__20____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__21____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__21____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__21____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__22____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__22____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__22____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__23____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__23____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__23____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__24____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__24____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__24____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__25____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__25____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__25____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__26____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__26____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__26____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__27____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__27____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__27____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__28____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__28____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__28____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__29____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__29____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__29____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__30____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__30____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__30____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__31____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__31____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__31____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__32____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__32____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__32____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__33____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__33____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__33____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__34____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__34____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__34____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__35____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__35____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__35____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__36____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__36____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__36____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__37____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__37____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__37____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__38____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__38____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__38____x40_Lean_CoreM___hyg_4814_);
l___auto___closed__39____x40_Lean_CoreM___hyg_4814_ = _init_l___auto___closed__39____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto___closed__39____x40_Lean_CoreM___hyg_4814_);
l___auto____x40_Lean_CoreM___hyg_4814_ = _init_l___auto____x40_Lean_CoreM___hyg_4814_();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_4814_);
l___auto____x40_Lean_CoreM___hyg_4955_ = _init_l___auto____x40_Lean_CoreM___hyg_4955_();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_4955_);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___closed__2);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___closed__0 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___lam__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__13___closed__0);
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
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__0 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__0();
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__1 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__1);
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__2 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__2);
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__3 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__3);
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__4 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__4();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__4);
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__5 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__5();
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__6 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__6();
l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__7 = _init_l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__7();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg___closed__7);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___closed__0 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___closed__0();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23_spec__23___closed__0);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__0 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__0);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__1);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__2);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__3);
l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__26___redArg___closed__4);
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
l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5857_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5857_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_5857_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5857_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5857_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_5857_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5857_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5857_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_5857_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5857_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5857_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_5857_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5857_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5857_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_5857_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5857_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5857_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_5857_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_5857_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_compiler_enableNew = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_compiler_enableNew);
lean_dec_ref(res);
}l_Lean_traceBlock___redArg___lam__2___closed__0 = _init_l_Lean_traceBlock___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_traceBlock___redArg___lam__2___closed__0);
l_Lean_traceBlock___redArg___closed__0 = _init_l_Lean_traceBlock___redArg___closed__0();
lean_mark_persistent(l_Lean_traceBlock___redArg___closed__0);
l_Lean_traceBlock___redArg___closed__1 = _init_l_Lean_traceBlock___redArg___closed__1();
lean_mark_persistent(l_Lean_traceBlock___redArg___closed__1);
l_Lean_compileDecls_doCompile___lam__1___closed__0 = _init_l_Lean_compileDecls_doCompile___lam__1___closed__0();
lean_mark_persistent(l_Lean_compileDecls_doCompile___lam__1___closed__0);
l_Lean_compileDecls_doCompile___lam__1___closed__1 = _init_l_Lean_compileDecls_doCompile___lam__1___closed__1();
lean_mark_persistent(l_Lean_compileDecls_doCompile___lam__1___closed__1);
l_Lean_compileDecls_doCompile___closed__0 = _init_l_Lean_compileDecls_doCompile___closed__0();
lean_mark_persistent(l_Lean_compileDecls_doCompile___closed__0);
l_Lean_compileDecls_doCompile___closed__1 = _init_l_Lean_compileDecls_doCompile___closed__1();
lean_mark_persistent(l_Lean_compileDecls_doCompile___closed__1);
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
l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7566_ = _init_l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7566_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_CoreM___hyg_7566_);
l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7566_ = _init_l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7566_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_CoreM___hyg_7566_);
l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7566_ = _init_l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7566_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_CoreM___hyg_7566_);
l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7566_ = _init_l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7566_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_CoreM___hyg_7566_);
l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7566_ = _init_l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7566_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_CoreM___hyg_7566_);
l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7566_ = _init_l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7566_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_CoreM___hyg_7566_);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_7566_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
