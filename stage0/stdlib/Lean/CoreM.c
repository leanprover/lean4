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
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__1;
static lean_object* l_Lean_Core_instMonadCoreM___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object*);
static double l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__8;
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instMonadExceptOfExceptionCoreM___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__5;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4(lean_object*);
lean_object* l_instBEqOfDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__7;
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_traceBlock(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1;
LEAN_EXPORT lean_object* l___auto____x40_Lean_CoreM___hyg_4116_;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_catchInternalIds___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantVal_instantiateTypeLevelParams(lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__1;
static lean_object* l_Lean_ImportM_runCoreM___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5_(lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___closed__3;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__6;
lean_object* l_Lean_Environment_constants(lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__9;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
static lean_object* l_Lean_compileDecls___lambda__2___closed__2;
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713_(lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__15;
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1;
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__14;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
lean_object* lean_io_get_tid(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__2;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_traceBlock___spec__1(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__2;
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__1;
static lean_object* l_Lean_Core_instMonadLogCoreM___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__5___boxed(lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__9;
static lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Name_getString_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM;
static lean_object* l_Lean_ImportM_runCoreM___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__37;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadInfoTreeCoreM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM;
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Core_saveState___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__22;
static lean_object* l_Lean_Core_getMaxHeartbeats___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isRealizing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Core_instMonadTraceCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__21;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___closed__1;
static lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__13;
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937_(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__6;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_casesOnSuffix;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM;
static lean_object* l_Lean_instMonadExceptOfExceptionCoreM___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___rarg___closed__7;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16;
lean_object* l_Array_qsort_sort___at_Lean_addTraceAsMessages___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadEnvCoreM___closed__2;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__17;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___rarg(lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__4;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instAddMessageContextCoreM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
static lean_object* l_Lean_Core_instMonadInfoTreeCoreM___closed__3;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_Core_wrapAsyncAsSnapshot___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__8;
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_lcnf_compile_decls(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_compileDecls___closed__2;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__5;
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__10;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__30;
LEAN_EXPORT lean_object* l_Lean_Core_saveState(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__10;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__8;
lean_object* l_EStateM_instMonad(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__7;
static uint64_t l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__9;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__2;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_40____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Core_instantiateTypeLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018_(lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14;
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___rarg(lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__1;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3;
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_Lean_Core_wrapAsync___elambda__1___spec__1(lean_object*);
static lean_object* l_Lean_Core_instMonadRefCoreM___closed__1;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__19;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_compileDecls_doCompile___spec__5___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCache___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls_doCompile___lambda__4___closed__1;
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__11;
static lean_object* l_Lean_Core_instMonadEnvCoreM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_catchInternalIds___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__26;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__6;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__7;
static lean_object* l_Lean_ImportM_runCoreM___rarg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at_Lean_compileDecls_doCompile___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__6;
lean_object* l_IO_CancelToken_new(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_Core_wrapAsyncAsSnapshot___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__4;
static lean_object* l_Lean_Core_instMonadLogCoreM___lambda__5___closed__2;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__6;
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__1;
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5;
LEAN_EXPORT lean_object* l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__3;
LEAN_EXPORT uint8_t l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__4;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25;
lean_object* l_Std_DHashMap_Internal_AssocList_getD___at_Lean_addTraceAsMessages___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM;
extern lean_object* l_ByteArray_empty;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__3;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_IO_addHeartbeats(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCache___closed__3;
static lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
lean_object* l_instDecidableEqPos___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__8;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__29;
static lean_object* l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___closed__1;
static lean_object* l_Lean_compileDecls___lambda__2___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Core_instMonadLogCoreM___lambda__5(lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__29;
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_Lean_Core_wrapAsync___elambda__1___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCoreM___rarg___closed__2;
static lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__15;
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___boxed(lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__14;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__4;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__31;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__12;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__1;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___closed__2;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__3;
LEAN_EXPORT lean_object* l___auto____x40_Lean_CoreM___hyg_3975_;
static lean_object* l_Lean_Core_instMonadRefCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_async;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__40;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__6;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_traceBlock___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadTraceCoreM___closed__2;
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__2;
static lean_object* l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__3___closed__1;
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__2;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDeclsOld___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadTraceCoreM___closed__1;
LEAN_EXPORT lean_object* l_Lean_compileDecls___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__10;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionCoreM(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___closed__1;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addTraceAsMessages___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__1;
LEAN_EXPORT lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___rarg___closed__1;
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__1;
static lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__1;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_compileDecls_doCompile___spec__5___rarg(lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__28;
static lean_object* l_Lean_Core_instMonadInfoTreeCoreM___closed__2;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__20;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__12;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__2;
extern lean_object* l_Task_Priority_default;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadResolveNameCoreM___closed__1;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__3;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__3(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__3;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__4;
static lean_object* l_Lean_instMonadExceptOfExceptionCoreM___closed__2;
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__2;
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDiag___boxed(lean_object*);
extern lean_object* l_Lean_warningAsError;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___boxed(lean_object**);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17;
lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams_x21(lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22;
static lean_object* l_Lean_Core_instMonadCoreM___closed__2;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192_(lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__2;
LEAN_EXPORT lean_object* l_Lean_catchInternalId___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__3;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__2;
static lean_object* l_Lean_mkArrow___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_PromiseCheckedResult_commitChecked(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lambda__3___closed__2;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__27;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Core_instantiateValueLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__6;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__2;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__32;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__4;
static lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28;
LEAN_EXPORT lean_object* l_Lean_compileDeclsNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19;
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__5;
static lean_object* l_Lean_mkArrow___closed__2;
lean_object* l_Lean_SMap_contains___at_Lean_Environment_addExtraName___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__2;
static lean_object* l_Lean_compileDecls_doCompile___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
static lean_object* l_Lean_useDiagnosticMsg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__9;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__7;
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__4;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadRefCoreM___closed__2;
static lean_object* l_Lean_Core_instInhabitedCache___closed__2;
static uint8_t l_Lean_ImportM_runCoreM___rarg___closed__9;
LEAN_EXPORT lean_object* l_Lean_compileDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__6;
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__3;
static lean_object* l_Lean_Core_resetMessageLog___closed__1;
static lean_object* l_Lean_compileDecls___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__4;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___rarg___closed__8;
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addTraceAsMessages___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__5;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__14;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__3;
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_compileDecls_doCompile___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_compileDecls_doCompile___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___rarg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153_(lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__9;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadTraceCoreM___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkArrowN___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__38;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at_Lean_compileDecls_doCompile___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_promiseChecked(lean_object*, lean_object*);
static lean_object* l_Lean_traceBlock___rarg___lambda__3___closed__2;
static lean_object* l_Lean_compileDecls___closed__1;
static lean_object* l_Lean_ImportM_runCoreM___rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__5;
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__2;
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_compileDecls_doCompile___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___boxed(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__6;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__18;
static lean_object* l_Lean_traceBlock___rarg___lambda__3___closed__1;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18;
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__10;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__11;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__11;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__2;
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__12;
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_traceBlock___rarg___lambda__2___closed__1;
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__8;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__24;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__4;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__2;
static lean_object* l_Lean_Core_instMonadCoreM___closed__3;
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_Core_wrapAsyncAsSnapshot___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___rarg(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__36;
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__8;
static lean_object* l_Lean_Core_instMonadCoreM___closed__6;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__13;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_compileDecls_doCompile___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__33;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_stderrAsMessages;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM;
LEAN_EXPORT lean_object* l_Lean_diagnostics_threshold;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Exception_isRuntime___boxed(lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkArrowN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__6;
LEAN_EXPORT lean_object* l_Lean_mapCoreM(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__1;
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__2;
LEAN_EXPORT lean_object* l_Lean_mkArrowN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_addTraceAsMessages___spec__16(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Core_instMonadResolveNameCoreM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
uint8_t l_Lean_PersistentArray_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(uint8_t, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___closed__1;
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__11;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__1;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__23;
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Core_instantiateValueLevelParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_compileDecls_doCompile___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Core_CoreM_toIO___rarg___closed__1;
static lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__35;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3(lean_object*);
static lean_object* l_Lean_Core_instMonadEnvCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__2;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_inServer;
LEAN_EXPORT lean_object* l_Lean_Core_instAddMessageContextCoreM;
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_debug_moduleNameAtTimeout;
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__4;
lean_object* l_instHashablePos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_traceBlock___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCache;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__25;
lean_object* l_Lean_Option_get_x3f___at_Lean_addTraceAsMessages___spec__17(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__7;
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__2;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__34;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__4;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__3;
LEAN_EXPORT uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lambda__3___closed__1;
extern lean_object* l_Lean_interruptExceptionId;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCoreM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addTraceAsMessages___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_maxHeartbeats;
static lean_object* l_Lean_Core_instMonadResolveNameCoreM___closed__3;
LEAN_EXPORT lean_object* l_Lean_internal_cmdlineSnapshots;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__13;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
lean_object* l_Lean_MessageLog_markAllReported(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getDiag(lean_object*);
static lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__4;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lambda__2___closed__4;
static lean_object* l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__1;
static lean_object* l_Lean_Core_throwMaxHeartbeat___closed__5;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2(lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__39;
static lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__1;
LEAN_EXPORT lean_object* l_Lean_compiler_enableNew;
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats___boxed(lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1;
double lean_float_sub(double, double);
static lean_object* l_Lean_compileDecls_doCompile___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
static lean_object* l___auto____x40_Lean_CoreM___hyg_3975____closed__16;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24;
static lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__1;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diagnostics", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("collect diagnostic information", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__2;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__4;
x_4 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("threshold", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only diagnostic counters above this threshold are reported by the definitional equality", 87, 87);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(20u);
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__2;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__4;
x_4 = l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__5;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_40____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxHeartbeats", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum amount of heartbeats per command. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit", 126, 126);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(200000u);
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__2;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__5;
x_4 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_40____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("async", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("perform elaboration using multiple threads where possible\n\nThis option defaults to `false` but (when not explicitly set) is overridden to `true` in the Lean language server and cmdline. Metaprogramming users driving elaboration directly via e.g. `Lean.Elab.Command.elabCommandTopLevel` can opt into asynchronous elaboration by setting this option but then are responsible for processing messages and other data not only in the resulting command state but also from async tasks in `Lean.Command.Context.snap\?` and `Lean.Command.State.snapshotTasks`.", 548, 548);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__3;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__5;
x_4 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inServer", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true if elaboration is being run inside the Lean language server\n\nThis option is set by the file worker and should not be modified otherwise.", 141, 141);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__2;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__4;
x_4 = l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__5;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cmdlineSnapshots", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__1;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduce information stored in snapshots to the minimum necessary for the cmdline driver: diagnostics per command and final full snapshot", 135, 135);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__1;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__3;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__5;
x_4 = l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_diagnostics;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_useDiagnosticMsg___lambda__2___closed__2;
x_5 = l_Lean_Name_toString(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nAdditional diagnostic information may be available using the `set_option ", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_useDiagnosticMsg___lambda__2___closed__4;
x_2 = l_Lean_useDiagnosticMsg___lambda__2___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" true` command.", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_useDiagnosticMsg___lambda__2___closed__5;
x_2 = l_Lean_useDiagnosticMsg___lambda__2___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg___lambda__2___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg___lambda__2___closed__8;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg___lambda__2___closed__10;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_5 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_useDiagnosticMsg___lambda__2___closed__9;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_useDiagnosticMsg___lambda__2___closed__11;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(invalid MessageData.lazy, missing context)", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg___lambda__3___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg___lambda__3___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_useDiagnosticMsg___lambda__3___closed__3;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_useDiagnosticMsg___closed__1;
x_2 = l_Lean_useDiagnosticMsg___lambda__2___closed__2;
x_3 = l_Lean_useDiagnosticMsg___closed__2;
x_4 = l_Lean_MessageData_lazy(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_useDiagnosticMsg___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_useDiagnosticMsg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lambda__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Kernel", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Core", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__3;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__5;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__7;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__9;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CoreM", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__10;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__12;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__14;
x_2 = lean_unsigned_to_nat(263u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__2;
x_3 = 0;
x_4 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__15;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_getMaxHeartbeats___closed__1() {
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
x_2 = l_Lean_Core_getMaxHeartbeats___closed__1;
x_3 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_2);
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
static lean_object* _init_l_Lean_Core_instInhabitedCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instInhabitedCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instInhabitedCache___closed__2;
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
x_1 = l_Lean_Core_instInhabitedCache___closed__3;
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
x_1 = l_EStateM_instMonad(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__2;
x_2 = l_ReaderT_instFunctorOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__2;
x_2 = l_ReaderT_instApplicativeOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__4;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = l_Lean_Core_instMonadCoreM___closed__3;
x_6 = l_Lean_Core_instMonadCoreM___closed__5;
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
x_7 = l_Lean_Core_instMonadCoreM___closed__6;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_12 = l_Lean_Core_instMonadCoreM___closed__3;
x_13 = l_Lean_Core_instMonadCoreM___closed__5;
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = l_Lean_Core_instMonadCoreM___closed__6;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadCoreM___closed__7;
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
x_2 = lean_alloc_ctor(1, 1, 0);
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
x_12 = l_Lean_Core_instInhabitedCache___closed__3;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_27 = lean_apply_1(x_1, x_20);
x_28 = l_Lean_Core_instInhabitedCache___closed__3;
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_29, 5, x_24);
lean_ctor_set(x_29, 6, x_25);
lean_ctor_set(x_29, 7, x_26);
x_30 = lean_st_ref_set(x_3, x_29, x_7);
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
static lean_object* _init_l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 4);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_dec(x_10);
x_11 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1;
x_12 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_11);
lean_ctor_set(x_5, 4, x_12);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*13, x_2);
x_13 = lean_apply_3(x_3, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get(x_5, 11);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_25 = lean_ctor_get(x_5, 12);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_26 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1;
x_27 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_26);
x_28 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_1);
lean_ctor_set(x_28, 3, x_16);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_17);
lean_ctor_set(x_28, 6, x_18);
lean_ctor_set(x_28, 7, x_19);
lean_ctor_set(x_28, 8, x_20);
lean_ctor_set(x_28, 9, x_21);
lean_ctor_set(x_28, 10, x_22);
lean_ctor_set(x_28, 11, x_23);
lean_ctor_set(x_28, 12, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 1, x_24);
x_29 = lean_apply_3(x_3, x_28, x_6, x_7);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_apply_1(x_1, x_6);
x_8 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_9 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_8);
x_10 = lean_st_ref_get(x_4, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Kernel_isDiagnosticsEnabled(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
if (x_9 == 0)
{
uint8_t x_45; 
x_45 = 1;
x_15 = x_45;
goto block_44;
}
else
{
uint8_t x_46; 
x_46 = 0;
x_15 = x_46;
goto block_44;
}
}
else
{
if (x_9 == 0)
{
uint8_t x_47; 
x_47 = 0;
x_15 = x_47;
goto block_44;
}
else
{
uint8_t x_48; 
x_48 = 1;
x_15 = x_48;
goto block_44;
}
}
block_44:
{
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_st_ref_take(x_4, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 4);
lean_dec(x_21);
x_22 = l_Lean_Kernel_enableDiag(x_20, x_9);
x_23 = l_Lean_Core_instInhabitedCache___closed__3;
lean_ctor_set(x_17, 4, x_23);
lean_ctor_set(x_17, 0, x_22);
x_24 = lean_st_ref_set(x_4, x_17, x_18);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_7, x_9, x_2, x_26, x_3, x_4, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
x_30 = lean_ctor_get(x_17, 2);
x_31 = lean_ctor_get(x_17, 3);
x_32 = lean_ctor_get(x_17, 5);
x_33 = lean_ctor_get(x_17, 6);
x_34 = lean_ctor_get(x_17, 7);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_35 = l_Lean_Kernel_enableDiag(x_28, x_9);
x_36 = l_Lean_Core_instInhabitedCache___closed__3;
x_37 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_32);
lean_ctor_set(x_37, 6, x_33);
lean_ctor_set(x_37, 7, x_34);
x_38 = lean_st_ref_set(x_4, x_37, x_18);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_7, x_9, x_2, x_40, x_3, x_4, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_7, x_9, x_2, x_42, x_3, x_4, x_12);
return x_43;
}
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_9;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 12);
lean_dec(x_11);
lean_inc(x_10);
lean_ctor_set(x_2, 12, x_7);
x_12 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_13 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_10, x_12);
x_14 = lean_st_ref_get(x_3, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Kernel_isDiagnosticsEnabled(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
if (x_13 == 0)
{
uint8_t x_49; 
x_49 = 1;
x_19 = x_49;
goto block_48;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_19 = x_50;
goto block_48;
}
}
else
{
if (x_13 == 0)
{
uint8_t x_51; 
x_51 = 0;
x_19 = x_51;
goto block_48;
}
else
{
uint8_t x_52; 
x_52 = 1;
x_19 = x_52;
goto block_48;
}
}
block_48:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_st_ref_take(x_3, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 4);
lean_dec(x_25);
x_26 = l_Lean_Kernel_enableDiag(x_24, x_13);
x_27 = l_Lean_Core_instInhabitedCache___closed__3;
lean_ctor_set(x_21, 4, x_27);
lean_ctor_set(x_21, 0, x_26);
x_28 = lean_st_ref_set(x_3, x_21, x_22);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_10, x_13, x_1, x_30, x_2, x_3, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
x_34 = lean_ctor_get(x_21, 2);
x_35 = lean_ctor_get(x_21, 3);
x_36 = lean_ctor_get(x_21, 5);
x_37 = lean_ctor_get(x_21, 6);
x_38 = lean_ctor_get(x_21, 7);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_39 = l_Lean_Kernel_enableDiag(x_32, x_13);
x_40 = l_Lean_Core_instInhabitedCache___closed__3;
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_35);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_36);
lean_ctor_set(x_41, 6, x_37);
lean_ctor_set(x_41, 7, x_38);
x_42 = lean_st_ref_set(x_3, x_41, x_22);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_10, x_13, x_1, x_44, x_2, x_3, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_10, x_13, x_1, x_46, x_2, x_3, x_16);
return x_47;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_ctor_get(x_2, 3);
x_57 = lean_ctor_get(x_2, 4);
x_58 = lean_ctor_get(x_2, 5);
x_59 = lean_ctor_get(x_2, 6);
x_60 = lean_ctor_get(x_2, 7);
x_61 = lean_ctor_get(x_2, 8);
x_62 = lean_ctor_get(x_2, 9);
x_63 = lean_ctor_get(x_2, 10);
x_64 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_65 = lean_ctor_get(x_2, 11);
x_66 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
lean_inc(x_65);
lean_inc(x_63);
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
lean_inc(x_55);
x_67 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_54);
lean_ctor_set(x_67, 2, x_55);
lean_ctor_set(x_67, 3, x_56);
lean_ctor_set(x_67, 4, x_57);
lean_ctor_set(x_67, 5, x_58);
lean_ctor_set(x_67, 6, x_59);
lean_ctor_set(x_67, 7, x_60);
lean_ctor_set(x_67, 8, x_61);
lean_ctor_set(x_67, 9, x_62);
lean_ctor_set(x_67, 10, x_63);
lean_ctor_set(x_67, 11, x_65);
lean_ctor_set(x_67, 12, x_7);
lean_ctor_set_uint8(x_67, sizeof(void*)*13, x_64);
lean_ctor_set_uint8(x_67, sizeof(void*)*13 + 1, x_66);
x_68 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_69 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_55, x_68);
x_70 = lean_st_ref_get(x_3, x_8);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Kernel_isDiagnosticsEnabled(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
if (x_69 == 0)
{
uint8_t x_97; 
x_97 = 1;
x_75 = x_97;
goto block_96;
}
else
{
uint8_t x_98; 
x_98 = 0;
x_75 = x_98;
goto block_96;
}
}
else
{
if (x_69 == 0)
{
uint8_t x_99; 
x_99 = 0;
x_75 = x_99;
goto block_96;
}
else
{
uint8_t x_100; 
x_100 = 1;
x_75 = x_100;
goto block_96;
}
}
block_96:
{
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_76 = lean_st_ref_take(x_3, x_72);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 5);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 6);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 7);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 lean_ctor_release(x_77, 6);
 lean_ctor_release(x_77, 7);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Kernel_enableDiag(x_79, x_69);
x_88 = l_Lean_Core_instInhabitedCache___closed__3;
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 8, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_80);
lean_ctor_set(x_89, 2, x_81);
lean_ctor_set(x_89, 3, x_82);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_83);
lean_ctor_set(x_89, 6, x_84);
lean_ctor_set(x_89, 7, x_85);
x_90 = lean_st_ref_set(x_3, x_89, x_78);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
x_93 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_55, x_69, x_1, x_92, x_67, x_3, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_box(0);
x_95 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_55, x_69, x_1, x_94, x_67, x_3, x_72);
return x_95;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Core_instInhabitedCache___closed__2;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__3;
x_3 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__2;
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
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_instInhabitedCache___closed__2;
x_3 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
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
x_10 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1;
x_11 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5;
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
x_18 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__1;
x_19 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__5;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_1);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_20);
lean_ctor_set(x_24, 5, x_21);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_7);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
x_35 = lean_ctor_get(x_6, 2);
x_36 = lean_ctor_get(x_6, 3);
x_37 = lean_ctor_get(x_6, 4);
x_38 = lean_ctor_get(x_6, 5);
x_39 = lean_ctor_get(x_6, 6);
x_40 = lean_ctor_get(x_6, 7);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_34, x_41);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_36);
lean_ctor_set(x_43, 4, x_37);
lean_ctor_set(x_43, 5, x_38);
lean_ctor_set(x_43, 6, x_39);
lean_ctor_set(x_43, 7, x_40);
x_44 = lean_st_ref_set(x_3, x_43, x_7);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 5);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 6);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 7);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 8);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 9);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_57 = lean_ctor_get(x_2, 11);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_59 = lean_ctor_get(x_2, 12);
lean_inc(x_59);
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
 x_60 = x_2;
} else {
 lean_dec_ref(x_2);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 13, 2);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_47);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_49);
lean_ctor_set(x_61, 4, x_50);
lean_ctor_set(x_61, 5, x_51);
lean_ctor_set(x_61, 6, x_52);
lean_ctor_set(x_61, 7, x_53);
lean_ctor_set(x_61, 8, x_54);
lean_ctor_set(x_61, 9, x_55);
lean_ctor_set(x_61, 10, x_34);
lean_ctor_set(x_61, 11, x_57);
lean_ctor_set(x_61, 12, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*13, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*13 + 1, x_58);
x_62 = lean_apply_3(x_1, x_61, x_3, x_45);
return x_62;
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 6);
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
x_10 = lean_ctor_get(x_8, 6);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_ctor_get(x_6, 6);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 6, x_10);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_26 = lean_apply_1(x_1, x_24);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_26);
lean_ctor_set(x_27, 7, x_25);
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
static lean_object* _init_l_Lean_Core_instMonadInfoTreeCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadInfoTreeCoreM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadInfoTreeCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadInfoTreeCoreM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadInfoTreeCoreM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadInfoTreeCoreM___closed__1;
x_2 = l_Lean_Core_instMonadInfoTreeCoreM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instMonadInfoTreeCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadInfoTreeCoreM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadInfoTreeCoreM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadInfoTreeCoreM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_26 = lean_apply_1(x_1, x_22);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 5);
x_35 = lean_ctor_get(x_6, 6);
x_36 = lean_ctor_get(x_6, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_39 = x_7;
} else {
 lean_dec_ref(x_7);
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
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_33);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_34);
lean_ctor_set(x_42, 6, x_35);
lean_ctor_set(x_42, 7, x_36);
x_43 = lean_st_ref_set(x_3, x_42, x_8);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 5);
x_35 = lean_ctor_get(x_6, 6);
x_36 = lean_ctor_get(x_6, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_39 = x_7;
} else {
 lean_dec_ref(x_7);
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
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_33);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_34);
lean_ctor_set(x_42, 6, x_35);
lean_ctor_set(x_42, 7, x_36);
x_43 = lean_st_ref_set(x_3, x_42, x_8);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Core_instantiateTypeLevelParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2;
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
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2;
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
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Core_instantiateTypeLevelParams___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Core_instantiateTypeLevelParams___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
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
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
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
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
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
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
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
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6(x_1, x_4, x_2);
return x_5;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
x_8 = lean_st_ref_take(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 4);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 0, x_2);
x_19 = l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_17, x_18, x_8);
lean_ctor_set(x_10, 0, x_19);
x_20 = lean_st_ref_set(x_5, x_9, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_7);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 0, x_2);
x_28 = l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_25, x_27, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_9, 4, x_29);
x_30 = lean_st_ref_set(x_5, x_9, x_12);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get(x_9, 2);
x_37 = lean_ctor_get(x_9, 3);
x_38 = lean_ctor_get(x_9, 5);
x_39 = lean_ctor_get(x_9, 6);
x_40 = lean_ctor_get(x_9, 7);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_41 = lean_ctor_get(x_10, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_43 = x_10;
} else {
 lean_dec_ref(x_10);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 0, x_2);
x_45 = l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_41, x_44, x_8);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 3, x_37);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_38);
lean_ctor_set(x_47, 6, x_39);
lean_ctor_set(x_47, 7, x_40);
x_48 = lean_st_ref_set(x_5, x_47, x_12);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_7);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_ctor_get(x_9, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_9, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_9, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_9, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_9, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_9, 7);
lean_inc(x_59);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 lean_ctor_release(x_9, 6);
 lean_ctor_release(x_9, 7);
 x_60 = x_9;
} else {
 lean_dec_ref(x_9);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_10, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_63 = x_10;
} else {
 lean_dec_ref(x_10);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
lean_inc(x_7);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_7);
x_66 = l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_61, x_64, x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
if (lean_is_scalar(x_60)) {
 x_68 = lean_alloc_ctor(0, 8, 0);
} else {
 x_68 = x_60;
}
lean_ctor_set(x_68, 0, x_53);
lean_ctor_set(x_68, 1, x_54);
lean_ctor_set(x_68, 2, x_55);
lean_ctor_set(x_68, 3, x_56);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_57);
lean_ctor_set(x_68, 6, x_58);
lean_ctor_set(x_68, 7, x_59);
x_69 = lean_st_ref_set(x_5, x_68, x_52);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_7);
lean_ctor_set(x_72, 1, x_70);
return x_72;
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
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(x_11, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_14 = lean_box(0);
x_15 = l_Lean_Core_instantiateTypeLevelParams___lambda__1(x_1, x_2, x_14, x_3, x_4, x_9);
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
return x_21;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
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
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(x_25, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Core_instantiateTypeLevelParams___lambda__1(x_1, x_2, x_28, x_3, x_4, x_23);
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
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_23);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Core_instantiateTypeLevelParams___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Core_instantiateTypeLevelParams___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Core_instantiateTypeLevelParams___spec__6(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
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
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Core_instantiateValueLevelParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_2);
x_7 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_8 = lean_st_ref_take(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 4);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 0, x_2);
x_19 = l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_17, x_18, x_8);
lean_ctor_set(x_10, 1, x_19);
x_20 = lean_st_ref_set(x_5, x_9, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_7);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 0, x_2);
x_28 = l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_26, x_27, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_9, 4, x_29);
x_30 = lean_st_ref_set(x_5, x_9, x_12);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get(x_9, 2);
x_37 = lean_ctor_get(x_9, 3);
x_38 = lean_ctor_get(x_9, 5);
x_39 = lean_ctor_get(x_9, 6);
x_40 = lean_ctor_get(x_9, 7);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_41 = lean_ctor_get(x_10, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_43 = x_10;
} else {
 lean_dec_ref(x_10);
 x_43 = lean_box(0);
}
x_44 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 0, x_2);
x_45 = l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_42, x_44, x_8);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 3, x_37);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_38);
lean_ctor_set(x_47, 6, x_39);
lean_ctor_set(x_47, 7, x_40);
x_48 = lean_st_ref_set(x_5, x_47, x_12);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_7);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_ctor_get(x_9, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_9, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_9, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_9, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_9, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_9, 7);
lean_inc(x_59);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 lean_ctor_release(x_9, 6);
 lean_ctor_release(x_9, 7);
 x_60 = x_9;
} else {
 lean_dec_ref(x_9);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_10, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_63 = x_10;
} else {
 lean_dec_ref(x_10);
 x_63 = lean_box(0);
}
x_64 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_7);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_7);
x_66 = l_Lean_PersistentHashMap_insert___at_Lean_Core_instantiateTypeLevelParams___spec__1(x_62, x_64, x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_60)) {
 x_68 = lean_alloc_ctor(0, 8, 0);
} else {
 x_68 = x_60;
}
lean_ctor_set(x_68, 0, x_53);
lean_ctor_set(x_68, 1, x_54);
lean_ctor_set(x_68, 2, x_55);
lean_ctor_set(x_68, 3, x_56);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_57);
lean_ctor_set(x_68, 6, x_58);
lean_ctor_set(x_68, 7, x_59);
x_69 = lean_st_ref_set(x_5, x_68, x_52);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_7);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
static lean_object* _init_l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not a definition or theorem: ", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; 
x_7 = 0;
x_8 = l_Lean_ConstantInfo_hasValue(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_2);
x_9 = l_Lean_ConstantInfo_name(x_1);
x_10 = l_Lean_MessageData_ofName(x_9);
x_11 = l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Core_instantiateValueLevelParams___spec__1(x_14, x_4, x_5, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Core_instantiateValueLevelParams___lambda__1(x_1, x_2, x_20, x_4, x_5, x_6);
return x_21;
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
x_13 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(x_11, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_14 = lean_box(0);
x_15 = l_Lean_Core_instantiateValueLevelParams___lambda__2(x_1, x_2, x_14, x_3, x_4, x_9);
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
x_21 = l_Lean_Core_instantiateValueLevelParams___lambda__2(x_1, x_2, x_20, x_3, x_4, x_9);
return x_21;
}
else
{
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
x_27 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Core_instantiateTypeLevelParams___spec__5(x_25, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Core_instantiateValueLevelParams___lambda__2(x_1, x_2, x_28, x_3, x_4, x_23);
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
x_35 = l_Lean_Core_instantiateValueLevelParams___lambda__2(x_1, x_2, x_34, x_3, x_4, x_23);
return x_35;
}
else
{
lean_object* x_36; 
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Core_instantiateValueLevelParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Core_instantiateValueLevelParams___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_instantiateValueLevelParams___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_dec(x_4);
lean_dec(x_3);
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
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
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
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
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
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
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
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_26 = lean_apply_1(x_1, x_21);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadTraceCoreM___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadTraceCoreM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_instMonadTraceCoreM___closed__1;
x_2 = l_Lean_Core_instMonadTraceCoreM___closed__2;
x_3 = l_Lean_Core_instMonadTraceCoreM___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_instMonadTraceCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadTraceCoreM___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Core_saveState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_saveState___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_saveState___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_saveState(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
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
x_10 = lean_apply_3(x_1, x_3, x_4, x_9);
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
x_39 = lean_apply_3(x_1, x_3, x_4, x_38);
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
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Core_withRestoreOrSaveFull___rarg___lambda__1(x_2, x_6, x_3, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_st_ref_set(x_4, x_11, x_5);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = l_IO_addHeartbeats(x_14, x_13);
lean_dec(x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_8);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_st_ref_set(x_4, x_22, x_5);
lean_dec(x_4);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
x_26 = l_IO_addHeartbeats(x_25, x_24);
lean_dec(x_25);
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
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
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
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_withRestoreOrSaveFull___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withRestoreOrSaveFull___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 5);
x_12 = lean_ctor_get(x_6, 6);
x_13 = lean_ctor_get(x_7, 6);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 5);
lean_dec(x_14);
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_ctor_set(x_7, 6, x_12);
lean_ctor_set(x_7, 5, x_11);
lean_ctor_set(x_7, 0, x_10);
x_16 = lean_st_ref_set(x_3, x_7, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 2);
x_28 = lean_ctor_get(x_7, 3);
x_29 = lean_ctor_get(x_7, 4);
x_30 = lean_ctor_get(x_7, 7);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_24);
lean_ctor_set(x_31, 6, x_25);
lean_ctor_set(x_31, 7, x_30);
x_32 = lean_st_ref_set(x_3, x_31, x_8);
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
x_18 = l_Lean_Environment_mainModule(x_17);
lean_dec(x_17);
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
x_23 = l_Lean_Environment_mainModule(x_22);
lean_dec(x_22);
x_24 = l_Lean_addMacroScope(x_23, x_1, x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_ctor_get(x_6, 3);
x_30 = lean_ctor_get(x_6, 4);
x_31 = lean_ctor_get(x_6, 5);
x_32 = lean_ctor_get(x_6, 6);
x_33 = lean_ctor_get(x_6, 7);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_27, x_34);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_29);
lean_ctor_set(x_36, 4, x_30);
lean_ctor_set(x_36, 5, x_31);
lean_ctor_set(x_36, 6, x_32);
lean_ctor_set(x_36, 7, x_33);
x_37 = lean_st_ref_set(x_3, x_36, x_7);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_get(x_3, x_38);
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
x_45 = l_Lean_addMacroScope(x_44, x_1, x_27);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_20 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1;
x_21 = lean_st_ref_get(x_20, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 12);
lean_dec(x_26);
lean_inc(x_25);
lean_ctor_set(x_2, 12, x_22);
x_27 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_28 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_25, x_27);
x_29 = lean_st_ref_get(x_6, x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Kernel_isDiagnosticsEnabled(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
if (x_28 == 0)
{
uint8_t x_82; 
x_82 = 1;
x_34 = x_82;
goto block_81;
}
else
{
uint8_t x_83; 
x_83 = 0;
x_34 = x_83;
goto block_81;
}
}
else
{
if (x_28 == 0)
{
uint8_t x_84; 
x_84 = 0;
x_34 = x_84;
goto block_81;
}
else
{
uint8_t x_85; 
x_85 = 1;
x_34 = x_85;
goto block_81;
}
}
block_81:
{
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_st_ref_take(x_6, x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 4);
lean_dec(x_40);
x_41 = l_Lean_Kernel_enableDiag(x_39, x_28);
x_42 = l_Lean_Core_instInhabitedCache___closed__3;
lean_ctor_set(x_36, 4, x_42);
lean_ctor_set(x_36, 0, x_41);
x_43 = lean_st_ref_set(x_6, x_36, x_37);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
lean_inc(x_6);
x_46 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_25, x_28, x_1, x_45, x_2, x_6, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_9 = x_47;
x_10 = x_48;
goto block_19;
}
else
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
x_55 = lean_ctor_get(x_36, 2);
x_56 = lean_ctor_get(x_36, 3);
x_57 = lean_ctor_get(x_36, 5);
x_58 = lean_ctor_get(x_36, 6);
x_59 = lean_ctor_get(x_36, 7);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
x_60 = l_Lean_Kernel_enableDiag(x_53, x_28);
x_61 = l_Lean_Core_instInhabitedCache___closed__3;
x_62 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_56);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_57);
lean_ctor_set(x_62, 6, x_58);
lean_ctor_set(x_62, 7, x_59);
x_63 = lean_st_ref_set(x_6, x_62, x_37);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_box(0);
lean_inc(x_6);
x_66 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_25, x_28, x_1, x_65, x_2, x_6, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_9 = x_67;
x_10 = x_68;
goto block_19;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_8);
lean_dec(x_6);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_box(0);
lean_inc(x_6);
x_74 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_25, x_28, x_1, x_73, x_2, x_6, x_31);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_9 = x_75;
x_10 = x_76;
goto block_19;
}
else
{
uint8_t x_77; 
lean_dec(x_8);
lean_dec(x_6);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_86 = lean_ctor_get(x_2, 0);
x_87 = lean_ctor_get(x_2, 1);
x_88 = lean_ctor_get(x_2, 2);
x_89 = lean_ctor_get(x_2, 3);
x_90 = lean_ctor_get(x_2, 4);
x_91 = lean_ctor_get(x_2, 5);
x_92 = lean_ctor_get(x_2, 6);
x_93 = lean_ctor_get(x_2, 7);
x_94 = lean_ctor_get(x_2, 8);
x_95 = lean_ctor_get(x_2, 9);
x_96 = lean_ctor_get(x_2, 10);
x_97 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_98 = lean_ctor_get(x_2, 11);
x_99 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
lean_inc(x_98);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_2);
lean_inc(x_88);
x_100 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_100, 0, x_86);
lean_ctor_set(x_100, 1, x_87);
lean_ctor_set(x_100, 2, x_88);
lean_ctor_set(x_100, 3, x_89);
lean_ctor_set(x_100, 4, x_90);
lean_ctor_set(x_100, 5, x_91);
lean_ctor_set(x_100, 6, x_92);
lean_ctor_set(x_100, 7, x_93);
lean_ctor_set(x_100, 8, x_94);
lean_ctor_set(x_100, 9, x_95);
lean_ctor_set(x_100, 10, x_96);
lean_ctor_set(x_100, 11, x_98);
lean_ctor_set(x_100, 12, x_22);
lean_ctor_set_uint8(x_100, sizeof(void*)*13, x_97);
lean_ctor_set_uint8(x_100, sizeof(void*)*13 + 1, x_99);
x_101 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_102 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_88, x_101);
x_103 = lean_st_ref_get(x_6, x_23);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Kernel_isDiagnosticsEnabled(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
if (x_102 == 0)
{
uint8_t x_142; 
x_142 = 1;
x_108 = x_142;
goto block_141;
}
else
{
uint8_t x_143; 
x_143 = 0;
x_108 = x_143;
goto block_141;
}
}
else
{
if (x_102 == 0)
{
uint8_t x_144; 
x_144 = 0;
x_108 = x_144;
goto block_141;
}
else
{
uint8_t x_145; 
x_145 = 1;
x_108 = x_145;
goto block_141;
}
}
block_141:
{
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_109 = lean_st_ref_take(x_6, x_105);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 5);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 6);
lean_inc(x_117);
x_118 = lean_ctor_get(x_110, 7);
lean_inc(x_118);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 lean_ctor_release(x_110, 6);
 lean_ctor_release(x_110, 7);
 x_119 = x_110;
} else {
 lean_dec_ref(x_110);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Kernel_enableDiag(x_112, x_102);
x_121 = l_Lean_Core_instInhabitedCache___closed__3;
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 8, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_113);
lean_ctor_set(x_122, 2, x_114);
lean_ctor_set(x_122, 3, x_115);
lean_ctor_set(x_122, 4, x_121);
lean_ctor_set(x_122, 5, x_116);
lean_ctor_set(x_122, 6, x_117);
lean_ctor_set(x_122, 7, x_118);
x_123 = lean_st_ref_set(x_6, x_122, x_111);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_box(0);
lean_inc(x_6);
x_126 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_88, x_102, x_1, x_125, x_100, x_6, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_9 = x_127;
x_10 = x_128;
goto block_19;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_8);
lean_dec(x_6);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_131 = x_126;
} else {
 lean_dec_ref(x_126);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_box(0);
lean_inc(x_6);
x_134 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_88, x_102, x_1, x_133, x_100, x_6, x_105);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_9 = x_135;
x_10 = x_136;
goto block_19;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_8);
lean_dec(x_6);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
block_19:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
if (lean_is_scalar(x_8)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_8;
}
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
if (lean_is_scalar(x_8)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_8;
}
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
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
lean_object* x_5; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_18 = lean_st_mk_ref(x_3, x_4);
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
x_33 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1;
x_34 = lean_st_ref_get(x_33, x_20);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; 
x_38 = lean_ctor_get(x_2, 2);
x_39 = lean_ctor_get(x_2, 12);
lean_dec(x_39);
lean_inc(x_38);
lean_ctor_set(x_2, 12, x_35);
x_40 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_41 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_38, x_40);
x_42 = lean_st_ref_get(x_19, x_36);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Kernel_isDiagnosticsEnabled(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
if (x_41 == 0)
{
uint8_t x_95; 
x_95 = 1;
x_47 = x_95;
goto block_94;
}
else
{
uint8_t x_96; 
x_96 = 0;
x_47 = x_96;
goto block_94;
}
}
else
{
if (x_41 == 0)
{
uint8_t x_97; 
x_97 = 0;
x_47 = x_97;
goto block_94;
}
else
{
uint8_t x_98; 
x_98 = 1;
x_47 = x_98;
goto block_94;
}
}
block_94:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_st_ref_take(x_19, x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 4);
lean_dec(x_53);
x_54 = l_Lean_Kernel_enableDiag(x_52, x_41);
x_55 = l_Lean_Core_instInhabitedCache___closed__3;
lean_ctor_set(x_49, 4, x_55);
lean_ctor_set(x_49, 0, x_54);
x_56 = lean_st_ref_set(x_19, x_49, x_50);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
lean_inc(x_19);
x_59 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_38, x_41, x_1, x_58, x_2, x_19, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_22 = x_60;
x_23 = x_61;
goto block_32;
}
else
{
uint8_t x_62; 
lean_dec(x_21);
lean_dec(x_19);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
x_5 = x_59;
goto block_17;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_5 = x_65;
goto block_17;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
x_68 = lean_ctor_get(x_49, 2);
x_69 = lean_ctor_get(x_49, 3);
x_70 = lean_ctor_get(x_49, 5);
x_71 = lean_ctor_get(x_49, 6);
x_72 = lean_ctor_get(x_49, 7);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
x_73 = l_Lean_Kernel_enableDiag(x_66, x_41);
x_74 = l_Lean_Core_instInhabitedCache___closed__3;
x_75 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_67);
lean_ctor_set(x_75, 2, x_68);
lean_ctor_set(x_75, 3, x_69);
lean_ctor_set(x_75, 4, x_74);
lean_ctor_set(x_75, 5, x_70);
lean_ctor_set(x_75, 6, x_71);
lean_ctor_set(x_75, 7, x_72);
x_76 = lean_st_ref_set(x_19, x_75, x_50);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_box(0);
lean_inc(x_19);
x_79 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_38, x_41, x_1, x_78, x_2, x_19, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_22 = x_80;
x_23 = x_81;
goto block_32;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_21);
lean_dec(x_19);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_84 = x_79;
} else {
 lean_dec_ref(x_79);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
x_5 = x_85;
goto block_17;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_box(0);
lean_inc(x_19);
x_87 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_38, x_41, x_1, x_86, x_2, x_19, x_44);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_22 = x_88;
x_23 = x_89;
goto block_32;
}
else
{
uint8_t x_90; 
lean_dec(x_21);
lean_dec(x_19);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
x_5 = x_87;
goto block_17;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_5 = x_93;
goto block_17;
}
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_121; 
x_99 = lean_ctor_get(x_2, 0);
x_100 = lean_ctor_get(x_2, 1);
x_101 = lean_ctor_get(x_2, 2);
x_102 = lean_ctor_get(x_2, 3);
x_103 = lean_ctor_get(x_2, 4);
x_104 = lean_ctor_get(x_2, 5);
x_105 = lean_ctor_get(x_2, 6);
x_106 = lean_ctor_get(x_2, 7);
x_107 = lean_ctor_get(x_2, 8);
x_108 = lean_ctor_get(x_2, 9);
x_109 = lean_ctor_get(x_2, 10);
x_110 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_111 = lean_ctor_get(x_2, 11);
x_112 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
lean_inc(x_111);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_2);
lean_inc(x_101);
x_113 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_113, 0, x_99);
lean_ctor_set(x_113, 1, x_100);
lean_ctor_set(x_113, 2, x_101);
lean_ctor_set(x_113, 3, x_102);
lean_ctor_set(x_113, 4, x_103);
lean_ctor_set(x_113, 5, x_104);
lean_ctor_set(x_113, 6, x_105);
lean_ctor_set(x_113, 7, x_106);
lean_ctor_set(x_113, 8, x_107);
lean_ctor_set(x_113, 9, x_108);
lean_ctor_set(x_113, 10, x_109);
lean_ctor_set(x_113, 11, x_111);
lean_ctor_set(x_113, 12, x_35);
lean_ctor_set_uint8(x_113, sizeof(void*)*13, x_110);
lean_ctor_set_uint8(x_113, sizeof(void*)*13 + 1, x_112);
x_114 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_115 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_101, x_114);
x_116 = lean_st_ref_get(x_19, x_36);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Kernel_isDiagnosticsEnabled(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
if (x_115 == 0)
{
uint8_t x_155; 
x_155 = 1;
x_121 = x_155;
goto block_154;
}
else
{
uint8_t x_156; 
x_156 = 0;
x_121 = x_156;
goto block_154;
}
}
else
{
if (x_115 == 0)
{
uint8_t x_157; 
x_157 = 0;
x_121 = x_157;
goto block_154;
}
else
{
uint8_t x_158; 
x_158 = 1;
x_121 = x_158;
goto block_154;
}
}
block_154:
{
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_122 = lean_st_ref_take(x_19, x_118);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 5);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 6);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 7);
lean_inc(x_131);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 lean_ctor_release(x_123, 6);
 lean_ctor_release(x_123, 7);
 x_132 = x_123;
} else {
 lean_dec_ref(x_123);
 x_132 = lean_box(0);
}
x_133 = l_Lean_Kernel_enableDiag(x_125, x_115);
x_134 = l_Lean_Core_instInhabitedCache___closed__3;
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 8, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_126);
lean_ctor_set(x_135, 2, x_127);
lean_ctor_set(x_135, 3, x_128);
lean_ctor_set(x_135, 4, x_134);
lean_ctor_set(x_135, 5, x_129);
lean_ctor_set(x_135, 6, x_130);
lean_ctor_set(x_135, 7, x_131);
x_136 = lean_st_ref_set(x_19, x_135, x_124);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_box(0);
lean_inc(x_19);
x_139 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_101, x_115, x_1, x_138, x_113, x_19, x_137);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_22 = x_140;
x_23 = x_141;
goto block_32;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_21);
lean_dec(x_19);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
x_5 = x_145;
goto block_17;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_box(0);
lean_inc(x_19);
x_147 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_101, x_115, x_1, x_146, x_113, x_19, x_118);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_22 = x_148;
x_23 = x_149;
goto block_32;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_21);
lean_dec(x_19);
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_152 = x_147;
} else {
 lean_dec_ref(x_147);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
x_5 = x_153;
goto block_17;
}
}
}
}
block_17:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
block_32:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_st_ref_get(x_19, x_23);
lean_dec(x_19);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_is_scalar(x_21)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_21;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_24, 0, x_27);
x_5 = x_24;
goto block_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
if (lean_is_scalar(x_21)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_21;
}
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_5 = x_31;
goto block_17;
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
x_1 = lean_mk_string_unchecked("internal exception #", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_io_get_num_heartbeats(x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_40 = lean_ctor_get(x_2, 2);
x_41 = lean_ctor_get(x_2, 12);
lean_dec(x_41);
x_42 = lean_ctor_get(x_2, 8);
lean_dec(x_42);
x_43 = lean_st_mk_ref(x_3, x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_58 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1;
x_59 = lean_st_ref_get(x_58, x_45);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_40);
lean_ctor_set(x_2, 12, x_60);
lean_ctor_set(x_2, 8, x_37);
x_62 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_63 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_40, x_62);
x_64 = lean_st_ref_get(x_44, x_61);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Kernel_isDiagnosticsEnabled(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
if (x_63 == 0)
{
uint8_t x_117; 
x_117 = 1;
x_69 = x_117;
goto block_116;
}
else
{
uint8_t x_118; 
x_118 = 0;
x_69 = x_118;
goto block_116;
}
}
else
{
if (x_63 == 0)
{
uint8_t x_119; 
x_119 = 0;
x_69 = x_119;
goto block_116;
}
else
{
uint8_t x_120; 
x_120 = 1;
x_69 = x_120;
goto block_116;
}
}
block_57:
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_st_ref_get(x_44, x_48);
lean_dec(x_44);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_49, 0, x_52);
x_5 = x_49;
goto block_35;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
if (lean_is_scalar(x_46)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_46;
}
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_5 = x_56;
goto block_35;
}
}
block_116:
{
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_st_ref_take(x_44, x_66);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = lean_ctor_get(x_71, 4);
lean_dec(x_75);
x_76 = l_Lean_Kernel_enableDiag(x_74, x_63);
x_77 = l_Lean_Core_instInhabitedCache___closed__3;
lean_ctor_set(x_71, 4, x_77);
lean_ctor_set(x_71, 0, x_76);
x_78 = lean_st_ref_set(x_44, x_71, x_72);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_box(0);
lean_inc(x_44);
x_81 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_40, x_63, x_1, x_80, x_2, x_44, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_47 = x_82;
x_48 = x_83;
goto block_57;
}
else
{
uint8_t x_84; 
lean_dec(x_46);
lean_dec(x_44);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
x_5 = x_81;
goto block_35;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_5 = x_87;
goto block_35;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_88 = lean_ctor_get(x_71, 0);
x_89 = lean_ctor_get(x_71, 1);
x_90 = lean_ctor_get(x_71, 2);
x_91 = lean_ctor_get(x_71, 3);
x_92 = lean_ctor_get(x_71, 5);
x_93 = lean_ctor_get(x_71, 6);
x_94 = lean_ctor_get(x_71, 7);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_71);
x_95 = l_Lean_Kernel_enableDiag(x_88, x_63);
x_96 = l_Lean_Core_instInhabitedCache___closed__3;
x_97 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_89);
lean_ctor_set(x_97, 2, x_90);
lean_ctor_set(x_97, 3, x_91);
lean_ctor_set(x_97, 4, x_96);
lean_ctor_set(x_97, 5, x_92);
lean_ctor_set(x_97, 6, x_93);
lean_ctor_set(x_97, 7, x_94);
x_98 = lean_st_ref_set(x_44, x_97, x_72);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_box(0);
lean_inc(x_44);
x_101 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_40, x_63, x_1, x_100, x_2, x_44, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_47 = x_102;
x_48 = x_103;
goto block_57;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_46);
lean_dec(x_44);
x_104 = lean_ctor_get(x_101, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_106 = x_101;
} else {
 lean_dec_ref(x_101);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
x_5 = x_107;
goto block_35;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_box(0);
lean_inc(x_44);
x_109 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_40, x_63, x_1, x_108, x_2, x_44, x_66);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_47 = x_110;
x_48 = x_111;
goto block_57;
}
else
{
uint8_t x_112; 
lean_dec(x_46);
lean_dec(x_44);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
x_5 = x_109;
goto block_35;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_5 = x_115;
goto block_35;
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; 
x_121 = lean_ctor_get(x_2, 0);
x_122 = lean_ctor_get(x_2, 1);
x_123 = lean_ctor_get(x_2, 2);
x_124 = lean_ctor_get(x_2, 3);
x_125 = lean_ctor_get(x_2, 4);
x_126 = lean_ctor_get(x_2, 5);
x_127 = lean_ctor_get(x_2, 6);
x_128 = lean_ctor_get(x_2, 7);
x_129 = lean_ctor_get(x_2, 9);
x_130 = lean_ctor_get(x_2, 10);
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_132 = lean_ctor_get(x_2, 11);
x_133 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
lean_inc(x_132);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_2);
x_134 = lean_st_mk_ref(x_3, x_38);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_147 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1;
x_148 = lean_st_ref_get(x_147, x_136);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
lean_inc(x_123);
x_151 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_151, 0, x_121);
lean_ctor_set(x_151, 1, x_122);
lean_ctor_set(x_151, 2, x_123);
lean_ctor_set(x_151, 3, x_124);
lean_ctor_set(x_151, 4, x_125);
lean_ctor_set(x_151, 5, x_126);
lean_ctor_set(x_151, 6, x_127);
lean_ctor_set(x_151, 7, x_128);
lean_ctor_set(x_151, 8, x_37);
lean_ctor_set(x_151, 9, x_129);
lean_ctor_set(x_151, 10, x_130);
lean_ctor_set(x_151, 11, x_132);
lean_ctor_set(x_151, 12, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*13, x_131);
lean_ctor_set_uint8(x_151, sizeof(void*)*13 + 1, x_133);
x_152 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_153 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_123, x_152);
x_154 = lean_st_ref_get(x_135, x_150);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Kernel_isDiagnosticsEnabled(x_157);
lean_dec(x_157);
if (x_158 == 0)
{
if (x_153 == 0)
{
uint8_t x_193; 
x_193 = 1;
x_159 = x_193;
goto block_192;
}
else
{
uint8_t x_194; 
x_194 = 0;
x_159 = x_194;
goto block_192;
}
}
else
{
if (x_153 == 0)
{
uint8_t x_195; 
x_195 = 0;
x_159 = x_195;
goto block_192;
}
else
{
uint8_t x_196; 
x_196 = 1;
x_159 = x_196;
goto block_192;
}
}
block_146:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_st_ref_get(x_135, x_139);
lean_dec(x_135);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_137;
}
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_141);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
x_5 = x_145;
goto block_35;
}
block_192:
{
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_160 = lean_st_ref_take(x_135, x_156);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_161, 5);
lean_inc(x_167);
x_168 = lean_ctor_get(x_161, 6);
lean_inc(x_168);
x_169 = lean_ctor_get(x_161, 7);
lean_inc(x_169);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 lean_ctor_release(x_161, 6);
 lean_ctor_release(x_161, 7);
 x_170 = x_161;
} else {
 lean_dec_ref(x_161);
 x_170 = lean_box(0);
}
x_171 = l_Lean_Kernel_enableDiag(x_163, x_153);
x_172 = l_Lean_Core_instInhabitedCache___closed__3;
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(0, 8, 0);
} else {
 x_173 = x_170;
}
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_165);
lean_ctor_set(x_173, 3, x_166);
lean_ctor_set(x_173, 4, x_172);
lean_ctor_set(x_173, 5, x_167);
lean_ctor_set(x_173, 6, x_168);
lean_ctor_set(x_173, 7, x_169);
x_174 = lean_st_ref_set(x_135, x_173, x_162);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_box(0);
lean_inc(x_135);
x_177 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_123, x_153, x_1, x_176, x_151, x_135, x_175);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_138 = x_178;
x_139 = x_179;
goto block_146;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_137);
lean_dec(x_135);
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_182 = x_177;
} else {
 lean_dec_ref(x_177);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
x_5 = x_183;
goto block_35;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_box(0);
lean_inc(x_135);
x_185 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_123, x_153, x_1, x_184, x_151, x_135, x_156);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_138 = x_186;
x_139 = x_187;
goto block_146;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_137);
lean_dec(x_135);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_190 = x_185;
} else {
 lean_dec_ref(x_185);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
x_5 = x_191;
goto block_35;
}
}
}
}
block_35:
{
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
lean_object* x_10; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_MessageData_toString(x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_5, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_25 = l_Lean_Core_CoreM_toIO___rarg___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_5, 0, x_27);
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = l___private_Init_Data_Repr_0__Nat_reprFast(x_29);
x_31 = l_Lean_Core_CoreM_toIO___rarg___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__6;
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
lean_object* x_44; 
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
x_44 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg(x_12, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_44;
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
x_5 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___rarg___lambda__1___boxed), 6, 2);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_withIncRecDepth___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_interruptExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 11);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_st_ref_get(x_7, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg(x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_checkInterrupted(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moduleNameAtTimeout", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__1;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("include module name in deterministic timeout error messages.\nRemark: we set this option to false to increase the stability of our test suite", 140, 140);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__1;
x_3 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__4;
x_3 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__1;
x_4 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__3;
x_3 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__5;
x_4 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_debug_moduleNameAtTimeout;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(deterministic) timeout", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_throwMaxHeartbeat___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", maximum number of heartbeats (", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_throwMaxHeartbeat___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") has been reached\nUse `set_option ", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_throwMaxHeartbeat___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" <num>` to set the limit.", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_throwMaxHeartbeat___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_throwMaxHeartbeat___closed__4;
x_2 = l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_throwMaxHeartbeat___closed__11;
x_2 = l_Lean_Core_throwMaxHeartbeat___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" at `", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = l_Lean_Core_throwMaxHeartbeat___closed__1;
x_9 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_8);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_unsigned_to_nat(1000u);
x_12 = lean_nat_div(x_3, x_11);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = l_Lean_MessageData_ofName(x_2);
if (x_9 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_17 = l_Lean_Core_throwMaxHeartbeat___closed__12;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = l_Lean_Core_throwMaxHeartbeat___closed__8;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = l_Lean_Core_throwMaxHeartbeat___closed__10;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_useDiagnosticMsg;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Core_throwMaxHeartbeat___closed__2;
x_29 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_inc(x_10);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_32 = 1;
x_33 = l_Lean_useDiagnosticMsg___lambda__2___closed__2;
x_34 = l_Lean_Name_toString(x_1, x_32, x_33);
x_35 = l_Lean_Core_throwMaxHeartbeat___closed__13;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_Core_throwMaxHeartbeat___closed__14;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = l_Lean_Core_throwMaxHeartbeat___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Core_throwMaxHeartbeat___closed__6;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_15);
x_45 = l_Lean_Core_throwMaxHeartbeat___closed__8;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_16);
x_48 = l_Lean_Core_throwMaxHeartbeat___closed__10;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_useDiagnosticMsg;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Core_throwMaxHeartbeat___closed__2;
x_55 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_inc(x_10);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_6);
return x_57;
}
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
x_6 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 11);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Core_checkMaxHeartbeats(x_1, x_2, x_3, x_4);
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
x_12 = l_Lean_Core_checkMaxHeartbeats(x_1, x_2, x_3, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get(x_6, 3);
x_21 = lean_ctor_get(x_6, 4);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_1);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_7);
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
static lean_object* _init_l_Lean_Core_resetMessageLog___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Core_resetMessageLog___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___rarg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_4, 5);
lean_inc(x_7);
x_8 = l_Lean_MessageLog_markAllReported(x_7);
lean_ctor_set(x_4, 5, x_8);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_17 = lean_ctor_get(x_4, 3);
x_18 = lean_ctor_get(x_4, 4);
x_19 = lean_ctor_get(x_4, 5);
x_20 = lean_ctor_get(x_4, 6);
x_21 = lean_ctor_get(x_4, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_19);
x_22 = l_Lean_MessageLog_markAllReported(x_19);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = lean_st_ref_set(x_1, x_23, x_5);
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
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_getAndEmptyMessageLog___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getAndEmptyMessageLog___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_getAndEmptyMessageLog(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___rarg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_4, 7);
x_8 = l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
lean_ctor_set(x_4, 7, x_8);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_17 = lean_ctor_get(x_4, 3);
x_18 = lean_ctor_get(x_4, 4);
x_19 = lean_ctor_get(x_4, 5);
x_20 = lean_ctor_get(x_4, 6);
x_21 = lean_ctor_get(x_4, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_22 = l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_22);
x_24 = lean_st_ref_set(x_1, x_23, x_5);
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
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_getAndEmptySnapshotTasks___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getAndEmptySnapshotTasks___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_getAndEmptySnapshotTasks(x_1);
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
x_12 = lean_ctor_get(x_10, 5);
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_3, 6);
x_9 = lean_ctor_get(x_3, 7);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_1, 4, x_11);
x_12 = lean_st_ref_take(x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 5);
x_17 = l_Lean_MessageLog_add(x_1, x_16);
lean_ctor_set(x_13, 5, x_17);
x_18 = lean_st_ref_set(x_4, x_13, x_14);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_27 = lean_ctor_get(x_13, 2);
x_28 = lean_ctor_get(x_13, 3);
x_29 = lean_ctor_get(x_13, 4);
x_30 = lean_ctor_get(x_13, 5);
x_31 = lean_ctor_get(x_13, 6);
x_32 = lean_ctor_get(x_13, 7);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_33 = l_Lean_MessageLog_add(x_1, x_30);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set(x_34, 3, x_28);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set(x_34, 6, x_31);
lean_ctor_set(x_34, 7, x_32);
x_35 = lean_st_ref_set(x_4, x_34, x_14);
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
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get(x_1, 2);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_46 = lean_ctor_get(x_1, 3);
x_47 = lean_ctor_get(x_1, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
x_48 = lean_ctor_get(x_3, 6);
x_49 = lean_ctor_get(x_3, 7);
lean_inc(x_49);
lean_inc(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_52, 2, x_42);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*5, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*5 + 1, x_44);
lean_ctor_set_uint8(x_52, sizeof(void*)*5 + 2, x_45);
x_53 = lean_st_ref_take(x_4, x_5);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_54, 6);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 7);
lean_inc(x_63);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 lean_ctor_release(x_54, 6);
 lean_ctor_release(x_54, 7);
 x_64 = x_54;
} else {
 lean_dec_ref(x_54);
 x_64 = lean_box(0);
}
x_65 = l_Lean_MessageLog_add(x_52, x_61);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 8, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_57);
lean_ctor_set(x_66, 2, x_58);
lean_ctor_set(x_66, 3, x_59);
lean_ctor_set(x_66, 4, x_60);
lean_ctor_set(x_66, 5, x_65);
lean_ctor_set(x_66, 6, x_62);
lean_ctor_set(x_66, 7, x_63);
x_67 = lean_st_ref_set(x_4, x_66, x_55);
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
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Core_instMonadLogCoreM___lambda__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Core_instMonadLogCoreM___lambda__5___closed__1;
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1;
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Core_instMonadLogCoreM___lambda__5___closed__2;
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Core_instMonadLogCoreM___lambda__5___closed__3;
x_15 = lean_string_dec_eq(x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Core_instMonadLogCoreM___lambda__5___closed__4;
x_17 = lean_string_dec_eq(x_7, x_16);
return x_17;
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
static lean_object* _init_l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lambda__5___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Core_instMonadLogCoreM___lambda__4(x_1, x_6, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
x_10 = l_Lean_MessageData_hasTag(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Core_instMonadLogCoreM___lambda__4(x_1, x_13, x_2, x_3, x_4);
return x_14;
}
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
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lambda__6___boxed), 4, 0);
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instMonadLogCoreM___lambda__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__5___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Core_instMonadLogCoreM___lambda__5(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadLogCoreM___lambda__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = lean_array_push(x_9, x_1);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_26 = lean_array_push(x_25, x_1);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_26);
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
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_Lean_Core_wrapAsync___elambda__1___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_Lean_Core_wrapAsync___elambda__1___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___at_Lean_Core_wrapAsync___elambda__1___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 4);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_dec(x_10);
x_11 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1;
x_12 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_11);
lean_ctor_set(x_5, 4, x_12);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*13, x_2);
x_13 = l_Lean_Core_withCurrHeartbeats___at_Lean_Core_wrapAsync___elambda__1___spec__1___rarg(x_3, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get(x_5, 11);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_25 = lean_ctor_get(x_5, 12);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_26 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1;
x_27 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_26);
x_28 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_1);
lean_ctor_set(x_28, 3, x_16);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_17);
lean_ctor_set(x_28, 6, x_18);
lean_ctor_set(x_28, 7, x_19);
lean_ctor_set(x_28, 8, x_20);
lean_ctor_set(x_28, 9, x_21);
lean_ctor_set(x_28, 10, x_22);
lean_ctor_set(x_28, 11, x_23);
lean_ctor_set(x_28, 12, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 1, x_24);
x_29 = l_Lean_Core_withCurrHeartbeats___at_Lean_Core_wrapAsync___elambda__1___spec__1___rarg(x_3, x_28, x_6, x_7);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15, uint8_t x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; 
x_20 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__1___boxed), 6, 3);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_18);
x_34 = lean_st_mk_ref(x_3, x_19);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
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
x_49 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1;
x_50 = lean_st_ref_get(x_49, x_36);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_6);
x_53 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_5);
lean_ctor_set(x_53, 2, x_6);
lean_ctor_set(x_53, 3, x_7);
lean_ctor_set(x_53, 4, x_8);
lean_ctor_set(x_53, 5, x_9);
lean_ctor_set(x_53, 6, x_10);
lean_ctor_set(x_53, 7, x_11);
lean_ctor_set(x_53, 8, x_12);
lean_ctor_set(x_53, 9, x_13);
lean_ctor_set(x_53, 10, x_14);
lean_ctor_set(x_53, 11, x_2);
lean_ctor_set(x_53, 12, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*13, x_15);
lean_ctor_set_uint8(x_53, sizeof(void*)*13 + 1, x_16);
x_54 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_55 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_6, x_54);
x_56 = lean_st_ref_get(x_35, x_52);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Kernel_isDiagnosticsEnabled(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
if (x_55 == 0)
{
uint8_t x_109; 
x_109 = 1;
x_61 = x_109;
goto block_108;
}
else
{
uint8_t x_110; 
x_110 = 0;
x_61 = x_110;
goto block_108;
}
}
else
{
if (x_55 == 0)
{
uint8_t x_111; 
x_111 = 0;
x_61 = x_111;
goto block_108;
}
else
{
uint8_t x_112; 
x_112 = 1;
x_61 = x_112;
goto block_108;
}
}
block_33:
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
block_48:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_st_ref_get(x_35, x_39);
lean_dec(x_35);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_40, 0, x_43);
x_21 = x_40;
goto block_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
if (lean_is_scalar(x_37)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_37;
}
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_21 = x_47;
goto block_33;
}
}
block_108:
{
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_st_ref_take(x_35, x_58);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 4);
lean_dec(x_67);
x_68 = l_Lean_Kernel_enableDiag(x_66, x_55);
x_69 = l_Lean_Core_instInhabitedCache___closed__3;
lean_ctor_set(x_63, 4, x_69);
lean_ctor_set(x_63, 0, x_68);
x_70 = lean_st_ref_set(x_35, x_63, x_64);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(0);
lean_inc(x_35);
x_73 = l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__2(x_6, x_55, x_20, x_72, x_53, x_35, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_38 = x_74;
x_39 = x_75;
goto block_48;
}
else
{
uint8_t x_76; 
lean_dec(x_37);
lean_dec(x_35);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
x_21 = x_73;
goto block_33;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_21 = x_79;
goto block_33;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_80 = lean_ctor_get(x_63, 0);
x_81 = lean_ctor_get(x_63, 1);
x_82 = lean_ctor_get(x_63, 2);
x_83 = lean_ctor_get(x_63, 3);
x_84 = lean_ctor_get(x_63, 5);
x_85 = lean_ctor_get(x_63, 6);
x_86 = lean_ctor_get(x_63, 7);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_63);
x_87 = l_Lean_Kernel_enableDiag(x_80, x_55);
x_88 = l_Lean_Core_instInhabitedCache___closed__3;
x_89 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_81);
lean_ctor_set(x_89, 2, x_82);
lean_ctor_set(x_89, 3, x_83);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_84);
lean_ctor_set(x_89, 6, x_85);
lean_ctor_set(x_89, 7, x_86);
x_90 = lean_st_ref_set(x_35, x_89, x_64);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
lean_inc(x_35);
x_93 = l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__2(x_6, x_55, x_20, x_92, x_53, x_35, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_38 = x_94;
x_39 = x_95;
goto block_48;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_37);
lean_dec(x_35);
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_98 = x_93;
} else {
 lean_dec_ref(x_93);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
x_21 = x_99;
goto block_33;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_box(0);
lean_inc(x_35);
x_101 = l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__2(x_6, x_55, x_20, x_100, x_53, x_35, x_58);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_38 = x_102;
x_39 = x_103;
goto block_48;
}
else
{
uint8_t x_104; 
lean_dec(x_37);
lean_dec(x_35);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
x_21 = x_101;
goto block_33;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_21 = x_107;
goto block_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___elambda__1___rarg___boxed), 19, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 10);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*13);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
lean_dec(x_3);
x_22 = lean_io_get_num_heartbeats(x_8);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_nat_sub(x_24, x_17);
lean_dec(x_24);
x_26 = lean_box(x_20);
x_27 = lean_box(x_21);
x_28 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___elambda__1___rarg___boxed), 19, 17);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_7);
lean_closure_set(x_28, 3, x_9);
lean_closure_set(x_28, 4, x_10);
lean_closure_set(x_28, 5, x_11);
lean_closure_set(x_28, 6, x_12);
lean_closure_set(x_28, 7, x_13);
lean_closure_set(x_28, 8, x_14);
lean_closure_set(x_28, 9, x_15);
lean_closure_set(x_28, 10, x_16);
lean_closure_set(x_28, 11, x_17);
lean_closure_set(x_28, 12, x_18);
lean_closure_set(x_28, 13, x_19);
lean_closure_set(x_28, 14, x_26);
lean_closure_set(x_28, 15, x_27);
lean_closure_set(x_28, 16, x_25);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_nat_sub(x_29, x_17);
lean_dec(x_29);
x_32 = lean_box(x_20);
x_33 = lean_box(x_21);
x_34 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___elambda__1___rarg___boxed), 19, 17);
lean_closure_set(x_34, 0, x_1);
lean_closure_set(x_34, 1, x_2);
lean_closure_set(x_34, 2, x_7);
lean_closure_set(x_34, 3, x_9);
lean_closure_set(x_34, 4, x_10);
lean_closure_set(x_34, 5, x_11);
lean_closure_set(x_34, 6, x_12);
lean_closure_set(x_34, 7, x_13);
lean_closure_set(x_34, 8, x_14);
lean_closure_set(x_34, 9, x_15);
lean_closure_set(x_34, 10, x_16);
lean_closure_set(x_34, 11, x_17);
lean_closure_set(x_34, 12, x_18);
lean_closure_set(x_34, 13, x_19);
lean_closure_set(x_34, 14, x_32);
lean_closure_set(x_34, 15, x_33);
lean_closure_set(x_34, 16, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Core_wrapAsync___elambda__1___rarg___lambda__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___elambda__1___rarg___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_15);
lean_dec(x_15);
x_21 = lean_unbox(x_16);
lean_dec(x_16);
x_22 = l_Lean_Core_wrapAsync___elambda__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_20, x_21, x_17, x_18, x_19);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsync___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stderrAsMessages", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("server", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message", 133, 133);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__3;
x_3 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__4;
x_3 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__2;
x_3 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__5;
x_4 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__1;
x_3 = l_Lean_Core_instMonadLogCoreM___lambda__5___closed__2;
x_4 = l___auto____x40_Lean_CoreM___hyg_3975____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__1;
x_3 = l_Lean_Core_instMonadLogCoreM___lambda__5___closed__2;
x_4 = l___auto____x40_Lean_CoreM___hyg_3975____closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__1;
x_3 = l_Lean_Core_instMonadLogCoreM___lambda__5___closed__2;
x_4 = l___auto____x40_Lean_CoreM___hyg_3975____closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__9;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__1;
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__13;
x_4 = l___auto____x40_Lean_CoreM___hyg_3975____closed__14;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__1;
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__13;
x_4 = l___auto____x40_Lean_CoreM___hyg_3975____closed__16;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl_name%", 10, 10);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__18;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__19;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__17;
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__20;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__21;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__23;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__22;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__24;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toString", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__26;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__26;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__27;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__26;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(2);
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__28;
x_4 = l___auto____x40_Lean_CoreM___hyg_3975____closed__29;
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__25;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__30;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__15;
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__31;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__12;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__32;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__10;
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__33;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__34;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__8;
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__35;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__36;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__6;
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__37;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__38;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__3;
x_3 = l___auto____x40_Lean_CoreM___hyg_3975____closed__39;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__40;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
x_10 = lean_ctor_get(x_1, 3);
x_11 = 0;
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_11);
x_13 = lean_ctor_get(x_1, 7);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = lean_ctor_get(x_1, 3);
x_19 = 0;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*4, x_19);
x_21 = lean_ctor_get(x_1, 7);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 5);
lean_inc(x_6);
x_7 = lean_string_utf8_byte_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
lean_dec(x_2);
x_13 = 0;
x_14 = l_Lean_Syntax_getPos_x3f(x_12, x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = l_Lean_MessageData_ofFormat(x_16);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = l_Lean_FileMap_toPosition(x_11, x_8);
x_19 = 0;
x_20 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_21 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 2, x_13);
x_22 = l_Lean_MessageLog_add(x_21, x_6);
x_23 = lean_box(0);
x_24 = l_Lean_Core_mkSnapshot___lambda__1(x_3, x_4, x_22, x_23, x_5);
lean_dec(x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = l_Lean_FileMap_toPosition(x_11, x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_29 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_15);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_17);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 2, x_13);
x_30 = l_Lean_MessageLog_add(x_29, x_6);
x_31 = lean_box(0);
x_32 = l_Lean_Core_mkSnapshot___lambda__1(x_3, x_4, x_30, x_31, x_5);
lean_dec(x_3);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = l_Lean_Core_mkSnapshot___lambda__1(x_3, x_4, x_6, x_33, x_5);
lean_dec(x_3);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_mkSnapshot___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_4116_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__40;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 12);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_checkTraceOption(x_5, x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 3);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
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
x_23 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
x_24 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint64(x_24, sizeof(void*)*1, x_22);
lean_ctor_set(x_9, 3, x_24);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 4);
x_33 = lean_ctor_get(x_9, 5);
x_34 = lean_ctor_get(x_9, 6);
x_35 = lean_ctor_get(x_9, 7);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_36 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_37 = x_10;
} else {
 lean_dec_ref(x_10);
 x_37 = lean_box(0);
}
x_38 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 1, 8);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_uint64(x_39, sizeof(void*)*1, x_36);
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_40, 4, x_32);
lean_ctor_set(x_40, 5, x_33);
lean_ctor_set(x_40, 6, x_34);
lean_ctor_set(x_40, 7, x_35);
x_41 = lean_st_ref_set(x_1, x_40, x_11);
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
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = lean_ctor_get(x_5, 5);
x_10 = l_Lean_replaceRef(x_3, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_10);
x_11 = lean_st_ref_get(x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_PersistentArray_toArray___rarg(x_15);
lean_dec(x_15);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(x_17, x_18, x_16);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_20, x_5, x_6, x_13);
lean_dec(x_5);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_6, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
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
x_31 = lean_ctor_get(x_25, 3);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_26, 0);
lean_dec(x_33);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 0, x_3);
x_34 = l_Lean_PersistentArray_push___rarg(x_1, x_24);
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
x_43 = l_Lean_PersistentArray_push___rarg(x_1, x_24);
x_44 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint64(x_44, sizeof(void*)*1, x_42);
lean_ctor_set(x_25, 3, x_44);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 1);
x_52 = lean_ctor_get(x_25, 2);
x_53 = lean_ctor_get(x_25, 4);
x_54 = lean_ctor_get(x_25, 5);
x_55 = lean_ctor_get(x_25, 6);
x_56 = lean_ctor_get(x_25, 7);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
x_57 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_58 = x_26;
} else {
 lean_dec_ref(x_26);
 x_58 = lean_box(0);
}
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 0, x_3);
x_59 = l_Lean_PersistentArray_push___rarg(x_1, x_24);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_57);
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set(x_61, 2, x_52);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_53);
lean_ctor_set(x_61, 5, x_54);
lean_ctor_set(x_61, 6, x_55);
lean_ctor_set(x_61, 7, x_56);
x_62 = lean_st_ref_set(x_6, x_61, x_28);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
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
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_67 = lean_ctor_get(x_24, 1);
lean_inc(x_67);
lean_dec(x_24);
x_68 = lean_ctor_get(x_25, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_25, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_25, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_25, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_25, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_25, 6);
lean_inc(x_73);
x_74 = lean_ctor_get(x_25, 7);
lean_inc(x_74);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 lean_ctor_release(x_25, 7);
 x_75 = x_25;
} else {
 lean_dec_ref(x_25);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_77 = x_26;
} else {
 lean_dec_ref(x_26);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_3);
lean_ctor_set(x_78, 1, x_22);
x_79 = l_Lean_PersistentArray_push___rarg(x_1, x_78);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 1, 8);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint64(x_80, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(0, 8, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_68);
lean_ctor_set(x_81, 1, x_69);
lean_ctor_set(x_81, 2, x_70);
lean_ctor_set(x_81, 3, x_80);
lean_ctor_set(x_81, 4, x_71);
lean_ctor_set(x_81, 5, x_72);
lean_ctor_set(x_81, 6, x_73);
lean_ctor_set(x_81, 7, x_74);
x_82 = lean_st_ref_set(x_6, x_81, x_67);
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
x_85 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint64_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_87 = lean_ctor_get(x_5, 0);
x_88 = lean_ctor_get(x_5, 1);
x_89 = lean_ctor_get(x_5, 2);
x_90 = lean_ctor_get(x_5, 3);
x_91 = lean_ctor_get(x_5, 4);
x_92 = lean_ctor_get(x_5, 5);
x_93 = lean_ctor_get(x_5, 6);
x_94 = lean_ctor_get(x_5, 7);
x_95 = lean_ctor_get(x_5, 8);
x_96 = lean_ctor_get(x_5, 9);
x_97 = lean_ctor_get(x_5, 10);
x_98 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_99 = lean_ctor_get(x_5, 11);
x_100 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_101 = lean_ctor_get(x_5, 12);
lean_inc(x_101);
lean_inc(x_99);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_5);
x_102 = l_Lean_replaceRef(x_3, x_92);
lean_dec(x_92);
x_103 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_103, 0, x_87);
lean_ctor_set(x_103, 1, x_88);
lean_ctor_set(x_103, 2, x_89);
lean_ctor_set(x_103, 3, x_90);
lean_ctor_set(x_103, 4, x_91);
lean_ctor_set(x_103, 5, x_102);
lean_ctor_set(x_103, 6, x_93);
lean_ctor_set(x_103, 7, x_94);
lean_ctor_set(x_103, 8, x_95);
lean_ctor_set(x_103, 9, x_96);
lean_ctor_set(x_103, 10, x_97);
lean_ctor_set(x_103, 11, x_99);
lean_ctor_set(x_103, 12, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*13, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*13 + 1, x_100);
x_104 = lean_st_ref_get(x_6, x_7);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 3);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_PersistentArray_toArray___rarg(x_108);
lean_dec(x_108);
x_110 = lean_array_size(x_109);
x_111 = 0;
x_112 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(x_110, x_111, x_109);
x_113 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_113, 0, x_2);
lean_ctor_set(x_113, 1, x_4);
lean_ctor_set(x_113, 2, x_112);
x_114 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_113, x_103, x_6, x_106);
lean_dec(x_103);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_st_ref_take(x_6, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_118, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_121 = x_117;
} else {
 lean_dec_ref(x_117);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_118, 5);
lean_inc(x_126);
x_127 = lean_ctor_get(x_118, 6);
lean_inc(x_127);
x_128 = lean_ctor_get(x_118, 7);
lean_inc(x_128);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 lean_ctor_release(x_118, 6);
 lean_ctor_release(x_118, 7);
 x_129 = x_118;
} else {
 lean_dec_ref(x_118);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get_uint64(x_119, sizeof(void*)*1);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_131 = x_119;
} else {
 lean_dec_ref(x_119);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_121;
}
lean_ctor_set(x_132, 0, x_3);
lean_ctor_set(x_132, 1, x_115);
x_133 = l_Lean_PersistentArray_push___rarg(x_1, x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 8);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set_uint64(x_134, sizeof(void*)*1, x_130);
if (lean_is_scalar(x_129)) {
 x_135 = lean_alloc_ctor(0, 8, 0);
} else {
 x_135 = x_129;
}
lean_ctor_set(x_135, 0, x_122);
lean_ctor_set(x_135, 1, x_123);
lean_ctor_set(x_135, 2, x_124);
lean_ctor_set(x_135, 3, x_134);
lean_ctor_set(x_135, 4, x_125);
lean_ctor_set(x_135, 5, x_126);
lean_ctor_set(x_135, 6, x_127);
lean_ctor_set(x_135, 7, x_128);
x_136 = lean_st_ref_set(x_6, x_135, x_120);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_box(0);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_7);
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(x_1, x_5, x_2, x_3, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(x_4, x_7, x_8, x_11);
lean_dec(x_7);
return x_12;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_7 == 0)
{
double x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set_float(x_15, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_15, sizeof(void*)*2 + 8, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 16, x_2);
x_16 = lean_box(0);
x_17 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__1(x_4, x_5, x_10, x_6, x_15, x_16, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_8);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_2);
x_19 = lean_box(0);
x_20 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__1(x_4, x_5, x_10, x_6, x_18, x_19, x_11, x_12, x_13);
return x_20;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, double x_7, double x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 5);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_15 = lean_apply_4(x_9, x_5, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_16, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__2;
x_21 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_20, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_5);
return x_21;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHeartbeats;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__1;
x_16 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_io_mono_nanos_now(x_14);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_10);
lean_inc(x_9);
x_114 = lean_apply_3(x_7, x_9, x_10, x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_119 = lean_io_mono_nanos_now(x_117);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; double x_125; double x_126; double x_127; double x_128; double x_129; lean_object* x_130; lean_object* x_131; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
x_123 = 0;
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Float_ofScientific(x_112, x_123, x_124);
lean_dec(x_112);
x_126 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_127 = lean_float_div(x_125, x_126);
x_128 = l_Float_ofScientific(x_121, x_123, x_124);
lean_dec(x_121);
x_129 = lean_float_div(x_128, x_126);
x_130 = lean_box_float(x_127);
x_131 = lean_box_float(x_129);
lean_ctor_set(x_119, 1, x_131);
lean_ctor_set(x_119, 0, x_130);
lean_ctor_set(x_114, 1, x_119);
lean_ctor_set(x_114, 0, x_118);
x_17 = x_114;
x_18 = x_122;
goto block_110;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; double x_136; double x_137; double x_138; double x_139; double x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_132 = lean_ctor_get(x_119, 0);
x_133 = lean_ctor_get(x_119, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_119);
x_134 = 0;
x_135 = lean_unsigned_to_nat(0u);
x_136 = l_Float_ofScientific(x_112, x_134, x_135);
lean_dec(x_112);
x_137 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_138 = lean_float_div(x_136, x_137);
x_139 = l_Float_ofScientific(x_132, x_134, x_135);
lean_dec(x_132);
x_140 = lean_float_div(x_139, x_137);
x_141 = lean_box_float(x_138);
x_142 = lean_box_float(x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_114, 1, x_143);
lean_ctor_set(x_114, 0, x_118);
x_17 = x_114;
x_18 = x_133;
goto block_110;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; double x_153; double x_154; double x_155; double x_156; double x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_144 = lean_ctor_get(x_114, 0);
x_145 = lean_ctor_get(x_114, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_114);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_144);
x_147 = lean_io_mono_nanos_now(x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = 0;
x_152 = lean_unsigned_to_nat(0u);
x_153 = l_Float_ofScientific(x_112, x_151, x_152);
lean_dec(x_112);
x_154 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_155 = lean_float_div(x_153, x_154);
x_156 = l_Float_ofScientific(x_148, x_151, x_152);
lean_dec(x_148);
x_157 = lean_float_div(x_156, x_154);
x_158 = lean_box_float(x_155);
x_159 = lean_box_float(x_157);
if (lean_is_scalar(x_150)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_150;
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_146);
lean_ctor_set(x_161, 1, x_160);
x_17 = x_161;
x_18 = x_149;
goto block_110;
}
}
else
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_114);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_114, 0);
x_164 = lean_ctor_get(x_114, 1);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_163);
x_166 = lean_io_mono_nanos_now(x_164);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; double x_172; double x_173; double x_174; double x_175; double x_176; lean_object* x_177; lean_object* x_178; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
x_170 = 0;
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_Float_ofScientific(x_112, x_170, x_171);
lean_dec(x_112);
x_173 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_174 = lean_float_div(x_172, x_173);
x_175 = l_Float_ofScientific(x_168, x_170, x_171);
lean_dec(x_168);
x_176 = lean_float_div(x_175, x_173);
x_177 = lean_box_float(x_174);
x_178 = lean_box_float(x_176);
lean_ctor_set(x_166, 1, x_178);
lean_ctor_set(x_166, 0, x_177);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 1, x_166);
lean_ctor_set(x_114, 0, x_165);
x_17 = x_114;
x_18 = x_169;
goto block_110;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; double x_183; double x_184; double x_185; double x_186; double x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_179 = lean_ctor_get(x_166, 0);
x_180 = lean_ctor_get(x_166, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_166);
x_181 = 0;
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Float_ofScientific(x_112, x_181, x_182);
lean_dec(x_112);
x_184 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_185 = lean_float_div(x_183, x_184);
x_186 = l_Float_ofScientific(x_179, x_181, x_182);
lean_dec(x_179);
x_187 = lean_float_div(x_186, x_184);
x_188 = lean_box_float(x_185);
x_189 = lean_box_float(x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 1, x_190);
lean_ctor_set(x_114, 0, x_165);
x_17 = x_114;
x_18 = x_180;
goto block_110;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; double x_200; double x_201; double x_202; double x_203; double x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_191 = lean_ctor_get(x_114, 0);
x_192 = lean_ctor_get(x_114, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_114);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_191);
x_194 = lean_io_mono_nanos_now(x_192);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = 0;
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Float_ofScientific(x_112, x_198, x_199);
lean_dec(x_112);
x_201 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_202 = lean_float_div(x_200, x_201);
x_203 = l_Float_ofScientific(x_195, x_198, x_199);
lean_dec(x_195);
x_204 = lean_float_div(x_203, x_201);
x_205 = lean_box_float(x_202);
x_206 = lean_box_float(x_204);
if (lean_is_scalar(x_197)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_197;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_193);
lean_ctor_set(x_208, 1, x_207);
x_17 = x_208;
x_18 = x_196;
goto block_110;
}
}
block_110:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
x_24 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_23);
if (x_24 == 0)
{
if (x_6 == 0)
{
uint8_t x_90; 
x_90 = 0;
x_25 = x_90;
goto block_89;
}
else
{
lean_object* x_91; double x_92; double x_93; lean_object* x_94; 
x_91 = lean_box(0);
x_92 = lean_unbox_float(x_21);
lean_dec(x_21);
x_93 = lean_unbox_float(x_22);
lean_dec(x_22);
x_94 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_92, x_93, x_5, x_91, x_9, x_10, x_18);
return x_94;
}
}
else
{
if (x_6 == 0)
{
double x_95; double x_96; double x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; double x_102; double x_103; double x_104; uint8_t x_105; 
x_95 = lean_unbox_float(x_22);
x_96 = lean_unbox_float(x_21);
x_97 = lean_float_sub(x_95, x_96);
x_98 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3;
x_99 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_98);
x_100 = 0;
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Float_ofScientific(x_99, x_100, x_101);
lean_dec(x_99);
x_103 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__4;
x_104 = lean_float_div(x_102, x_103);
x_105 = lean_float_decLt(x_104, x_97);
x_25 = x_105;
goto block_89;
}
else
{
lean_object* x_106; double x_107; double x_108; lean_object* x_109; 
x_106 = lean_box(0);
x_107 = lean_unbox_float(x_21);
lean_dec(x_21);
x_108 = lean_unbox_float(x_22);
lean_dec(x_22);
x_109 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_107, x_108, x_5, x_106, x_9, x_10, x_18);
return x_109;
}
}
block_89:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_st_ref_take(x_10, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 3);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = l_Lean_PersistentArray_append___rarg(x_13, x_33);
lean_dec(x_33);
lean_ctor_set(x_28, 0, x_34);
x_35 = lean_st_ref_set(x_10, x_27, x_29);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(x_20, x_9, x_10, x_36);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
lean_dec(x_28);
x_48 = l_Lean_PersistentArray_append___rarg(x_13, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint64(x_49, sizeof(void*)*1, x_46);
lean_ctor_set(x_27, 3, x_49);
x_50 = lean_st_ref_set(x_10, x_27, x_29);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(x_20, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
x_63 = lean_ctor_get(x_27, 2);
x_64 = lean_ctor_get(x_27, 4);
x_65 = lean_ctor_get(x_27, 5);
x_66 = lean_ctor_get(x_27, 6);
x_67 = lean_ctor_get(x_27, 7);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_68 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_69 = lean_ctor_get(x_28, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_70 = x_28;
} else {
 lean_dec_ref(x_28);
 x_70 = lean_box(0);
}
x_71 = l_Lean_PersistentArray_append___rarg(x_13, x_69);
lean_dec(x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_68);
x_73 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_62);
lean_ctor_set(x_73, 2, x_63);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_64);
lean_ctor_set(x_73, 5, x_65);
lean_ctor_set(x_73, 6, x_66);
lean_ctor_set(x_73, 7, x_67);
x_74 = lean_st_ref_set(x_10, x_73, x_29);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(x_20, x_9, x_10, x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; double x_86; double x_87; lean_object* x_88; 
x_85 = lean_box(0);
x_86 = lean_unbox_float(x_21);
lean_dec(x_21);
x_87 = lean_unbox_float(x_22);
lean_dec(x_22);
x_88 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_86, x_87, x_5, x_85, x_9, x_10, x_18);
return x_88;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_io_get_num_heartbeats(x_14);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
lean_inc(x_10);
lean_inc(x_9);
x_304 = lean_apply_3(x_7, x_9, x_10, x_303);
if (lean_obj_tag(x_304) == 0)
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = lean_ctor_get(x_304, 1);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_306);
x_309 = lean_io_get_num_heartbeats(x_307);
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; double x_315; double x_316; lean_object* x_317; lean_object* x_318; 
x_311 = lean_ctor_get(x_309, 0);
x_312 = lean_ctor_get(x_309, 1);
x_313 = 0;
x_314 = lean_unsigned_to_nat(0u);
x_315 = l_Float_ofScientific(x_302, x_313, x_314);
lean_dec(x_302);
x_316 = l_Float_ofScientific(x_311, x_313, x_314);
lean_dec(x_311);
x_317 = lean_box_float(x_315);
x_318 = lean_box_float(x_316);
lean_ctor_set(x_309, 1, x_318);
lean_ctor_set(x_309, 0, x_317);
lean_ctor_set(x_304, 1, x_309);
lean_ctor_set(x_304, 0, x_308);
x_209 = x_304;
x_210 = x_312;
goto block_300;
}
else
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; double x_323; double x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = lean_ctor_get(x_309, 0);
x_320 = lean_ctor_get(x_309, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_309);
x_321 = 0;
x_322 = lean_unsigned_to_nat(0u);
x_323 = l_Float_ofScientific(x_302, x_321, x_322);
lean_dec(x_302);
x_324 = l_Float_ofScientific(x_319, x_321, x_322);
lean_dec(x_319);
x_325 = lean_box_float(x_323);
x_326 = lean_box_float(x_324);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set(x_304, 1, x_327);
lean_ctor_set(x_304, 0, x_308);
x_209 = x_304;
x_210 = x_320;
goto block_300;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; double x_337; double x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_328 = lean_ctor_get(x_304, 0);
x_329 = lean_ctor_get(x_304, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_304);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_328);
x_331 = lean_io_get_num_heartbeats(x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_334 = x_331;
} else {
 lean_dec_ref(x_331);
 x_334 = lean_box(0);
}
x_335 = 0;
x_336 = lean_unsigned_to_nat(0u);
x_337 = l_Float_ofScientific(x_302, x_335, x_336);
lean_dec(x_302);
x_338 = l_Float_ofScientific(x_332, x_335, x_336);
lean_dec(x_332);
x_339 = lean_box_float(x_337);
x_340 = lean_box_float(x_338);
if (lean_is_scalar(x_334)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_334;
}
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_330);
lean_ctor_set(x_342, 1, x_341);
x_209 = x_342;
x_210 = x_333;
goto block_300;
}
}
else
{
uint8_t x_343; 
x_343 = !lean_is_exclusive(x_304);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_344 = lean_ctor_get(x_304, 0);
x_345 = lean_ctor_get(x_304, 1);
x_346 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_346, 0, x_344);
x_347 = lean_io_get_num_heartbeats(x_345);
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; double x_353; double x_354; lean_object* x_355; lean_object* x_356; 
x_349 = lean_ctor_get(x_347, 0);
x_350 = lean_ctor_get(x_347, 1);
x_351 = 0;
x_352 = lean_unsigned_to_nat(0u);
x_353 = l_Float_ofScientific(x_302, x_351, x_352);
lean_dec(x_302);
x_354 = l_Float_ofScientific(x_349, x_351, x_352);
lean_dec(x_349);
x_355 = lean_box_float(x_353);
x_356 = lean_box_float(x_354);
lean_ctor_set(x_347, 1, x_356);
lean_ctor_set(x_347, 0, x_355);
lean_ctor_set_tag(x_304, 0);
lean_ctor_set(x_304, 1, x_347);
lean_ctor_set(x_304, 0, x_346);
x_209 = x_304;
x_210 = x_350;
goto block_300;
}
else
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; double x_361; double x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_357 = lean_ctor_get(x_347, 0);
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_347);
x_359 = 0;
x_360 = lean_unsigned_to_nat(0u);
x_361 = l_Float_ofScientific(x_302, x_359, x_360);
lean_dec(x_302);
x_362 = l_Float_ofScientific(x_357, x_359, x_360);
lean_dec(x_357);
x_363 = lean_box_float(x_361);
x_364 = lean_box_float(x_362);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
lean_ctor_set_tag(x_304, 0);
lean_ctor_set(x_304, 1, x_365);
lean_ctor_set(x_304, 0, x_346);
x_209 = x_304;
x_210 = x_358;
goto block_300;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; double x_375; double x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_366 = lean_ctor_get(x_304, 0);
x_367 = lean_ctor_get(x_304, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_304);
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_366);
x_369 = lean_io_get_num_heartbeats(x_367);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_372 = x_369;
} else {
 lean_dec_ref(x_369);
 x_372 = lean_box(0);
}
x_373 = 0;
x_374 = lean_unsigned_to_nat(0u);
x_375 = l_Float_ofScientific(x_302, x_373, x_374);
lean_dec(x_302);
x_376 = l_Float_ofScientific(x_370, x_373, x_374);
lean_dec(x_370);
x_377 = lean_box_float(x_375);
x_378 = lean_box_float(x_376);
if (lean_is_scalar(x_372)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_372;
}
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_368);
lean_ctor_set(x_380, 1, x_379);
x_209 = x_380;
x_210 = x_371;
goto block_300;
}
}
block_300:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; 
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
x_216 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_215);
if (x_216 == 0)
{
if (x_6 == 0)
{
uint8_t x_282; 
x_282 = 0;
x_217 = x_282;
goto block_281;
}
else
{
lean_object* x_283; double x_284; double x_285; lean_object* x_286; 
x_283 = lean_box(0);
x_284 = lean_unbox_float(x_213);
lean_dec(x_213);
x_285 = lean_unbox_float(x_214);
lean_dec(x_214);
x_286 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_212, x_216, x_284, x_285, x_5, x_283, x_9, x_10, x_210);
return x_286;
}
}
else
{
if (x_6 == 0)
{
double x_287; double x_288; double x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; double x_294; uint8_t x_295; 
x_287 = lean_unbox_float(x_214);
x_288 = lean_unbox_float(x_213);
x_289 = lean_float_sub(x_287, x_288);
x_290 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3;
x_291 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_290);
x_292 = 0;
x_293 = lean_unsigned_to_nat(0u);
x_294 = l_Float_ofScientific(x_291, x_292, x_293);
lean_dec(x_291);
x_295 = lean_float_decLt(x_294, x_289);
x_217 = x_295;
goto block_281;
}
else
{
lean_object* x_296; double x_297; double x_298; lean_object* x_299; 
x_296 = lean_box(0);
x_297 = lean_unbox_float(x_213);
lean_dec(x_213);
x_298 = lean_unbox_float(x_214);
lean_dec(x_214);
x_299 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_212, x_216, x_297, x_298, x_5, x_296, x_9, x_10, x_210);
return x_299;
}
}
block_281:
{
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_218 = lean_st_ref_take(x_10, x_210);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = !lean_is_exclusive(x_219);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_219, 3);
lean_dec(x_223);
x_224 = !lean_is_exclusive(x_220);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_220, 0);
x_226 = l_Lean_PersistentArray_append___rarg(x_13, x_225);
lean_dec(x_225);
lean_ctor_set(x_220, 0, x_226);
x_227 = lean_st_ref_set(x_10, x_219, x_221);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(x_212, x_9, x_10, x_228);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
return x_229;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_229);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
else
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_229);
if (x_234 == 0)
{
return x_229;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_229, 0);
x_236 = lean_ctor_get(x_229, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_229);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint64_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_ctor_get_uint64(x_220, sizeof(void*)*1);
x_239 = lean_ctor_get(x_220, 0);
lean_inc(x_239);
lean_dec(x_220);
x_240 = l_Lean_PersistentArray_append___rarg(x_13, x_239);
lean_dec(x_239);
x_241 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set_uint64(x_241, sizeof(void*)*1, x_238);
lean_ctor_set(x_219, 3, x_241);
x_242 = lean_st_ref_set(x_10, x_219, x_221);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(x_212, x_9, x_10, x_243);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_244, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint64_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_253 = lean_ctor_get(x_219, 0);
x_254 = lean_ctor_get(x_219, 1);
x_255 = lean_ctor_get(x_219, 2);
x_256 = lean_ctor_get(x_219, 4);
x_257 = lean_ctor_get(x_219, 5);
x_258 = lean_ctor_get(x_219, 6);
x_259 = lean_ctor_get(x_219, 7);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_219);
x_260 = lean_ctor_get_uint64(x_220, sizeof(void*)*1);
x_261 = lean_ctor_get(x_220, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_262 = x_220;
} else {
 lean_dec_ref(x_220);
 x_262 = lean_box(0);
}
x_263 = l_Lean_PersistentArray_append___rarg(x_13, x_261);
lean_dec(x_261);
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 1, 8);
} else {
 x_264 = x_262;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set_uint64(x_264, sizeof(void*)*1, x_260);
x_265 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_265, 0, x_253);
lean_ctor_set(x_265, 1, x_254);
lean_ctor_set(x_265, 2, x_255);
lean_ctor_set(x_265, 3, x_264);
lean_ctor_set(x_265, 4, x_256);
lean_ctor_set(x_265, 5, x_257);
lean_ctor_set(x_265, 6, x_258);
lean_ctor_set(x_265, 7, x_259);
x_266 = lean_st_ref_set(x_10, x_265, x_221);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(x_212, x_9, x_10, x_267);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_268, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_275 = x_268;
} else {
 lean_dec_ref(x_268);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
}
else
{
lean_object* x_277; double x_278; double x_279; lean_object* x_280; 
x_277 = lean_box(0);
x_278 = lean_unbox_float(x_213);
lean_dec(x_213);
x_279 = lean_unbox_float(x_214);
lean_dec(x_214);
x_280 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_212, x_216, x_278, x_279, x_5, x_277, x_9, x_10, x_210);
return x_280;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2(x_1, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
x_15 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_apply_3(x_3, x_6, x_7, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_11);
lean_dec(x_11);
x_27 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4(x_9, x_1, x_4, x_5, x_2, x_26, x_3, x_25, x_6, x_7, x_13);
lean_dec(x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_box(0);
x_30 = lean_unbox(x_11);
lean_dec(x_11);
x_31 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4(x_9, x_1, x_4, x_5, x_2, x_30, x_3, x_29, x_6, x_7, x_28);
lean_dec(x_9);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_10, x_9);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_uget(x_8, x_10);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 1);
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
lean_inc(x_19);
lean_inc(x_3);
x_21 = l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8(x_1, x_2, x_3, x_4, x_17, x_19, x_12, x_13, x_14);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_11, 0, x_25);
lean_ctor_set(x_21, 0, x_11);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_11, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
lean_dec(x_19);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
lean_inc(x_7);
lean_ctor_set(x_11, 1, x_30);
lean_ctor_set(x_11, 0, x_7);
x_31 = 1;
x_32 = lean_usize_add(x_10, x_31);
x_10 = x_32;
x_14 = x_29;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_dec(x_11);
lean_inc(x_34);
lean_inc(x_3);
x_35 = l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8(x_1, x_2, x_3, x_4, x_17, x_34, x_12, x_13, x_14);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_7);
lean_dec(x_3);
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
lean_ctor_set(x_40, 1, x_34);
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
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_inc(x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_10, x_45);
x_10 = x_46;
x_11 = x_44;
x_14 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_9, x_8);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_array_uget(x_7, x_9);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 5);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Lean_Syntax_getPos_x3f(x_20, x_21);
x_23 = l_Lean_Syntax_getTailPos_x3f(x_20, x_21);
lean_dec(x_20);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_125; 
x_125 = lean_unsigned_to_nat(0u);
x_25 = x_125;
goto block_124;
}
else
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_22, 0);
lean_inc(x_126);
lean_dec(x_22);
x_25 = x_126;
goto block_124;
}
block_124:
{
lean_object* x_26; 
if (lean_obj_tag(x_23) == 0)
{
lean_inc(x_25);
x_26 = x_25;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_23, 0);
lean_inc(x_123);
lean_dec(x_23);
x_26 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_26);
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
x_31 = lean_array_get_size(x_30);
x_32 = lean_uint64_of_nat(x_25);
lean_dec(x_25);
x_33 = lean_uint64_of_nat(x_26);
lean_dec(x_26);
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
x_46 = lean_array_uget(x_30, x_45);
x_47 = l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
x_48 = l_Std_DHashMap_Internal_AssocList_getD___at_Lean_addTraceAsMessages___spec__1(x_27, x_47, x_46);
x_49 = lean_array_push(x_48, x_24);
x_50 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addTraceAsMessages___spec__2(x_27, x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_29, x_51);
lean_dec(x_29);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_27);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_46);
x_54 = lean_array_uset(x_30, x_45, x_53);
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_nat_mul(x_52, x_55);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_nat_div(x_56, x_57);
lean_dec(x_56);
x_59 = lean_array_get_size(x_54);
x_60 = lean_nat_dec_le(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; size_t x_63; 
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addTraceAsMessages___spec__3(x_54);
lean_ctor_set(x_17, 1, x_61);
lean_ctor_set(x_17, 0, x_52);
lean_inc(x_6);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_6);
lean_ctor_set(x_62, 1, x_17);
x_63 = lean_usize_add(x_9, x_43);
x_9 = x_63;
x_10 = x_62;
goto _start;
}
else
{
lean_object* x_65; size_t x_66; 
lean_ctor_set(x_17, 1, x_54);
lean_ctor_set(x_17, 0, x_52);
lean_inc(x_6);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_17);
x_66 = lean_usize_add(x_9, x_43);
x_9 = x_66;
x_10 = x_65;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; 
lean_inc(x_3);
x_68 = lean_array_uset(x_30, x_45, x_3);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addTraceAsMessages___spec__7(x_27, x_49, x_46);
x_70 = lean_array_uset(x_68, x_45, x_69);
lean_ctor_set(x_17, 1, x_70);
lean_inc(x_6);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_6);
lean_ctor_set(x_71, 1, x_17);
x_72 = lean_usize_add(x_9, x_43);
x_9 = x_72;
x_10 = x_71;
goto _start;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_74 = lean_ctor_get(x_17, 0);
x_75 = lean_ctor_get(x_17, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_17);
x_76 = lean_array_get_size(x_75);
x_77 = lean_uint64_of_nat(x_25);
lean_dec(x_25);
x_78 = lean_uint64_of_nat(x_26);
lean_dec(x_26);
x_79 = lean_uint64_mix_hash(x_77, x_78);
x_80 = 32;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = 16;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_uint64_xor(x_82, x_84);
x_86 = lean_uint64_to_usize(x_85);
x_87 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_88 = 1;
x_89 = lean_usize_sub(x_87, x_88);
x_90 = lean_usize_land(x_86, x_89);
x_91 = lean_array_uget(x_75, x_90);
x_92 = l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
x_93 = l_Std_DHashMap_Internal_AssocList_getD___at_Lean_addTraceAsMessages___spec__1(x_27, x_92, x_91);
x_94 = lean_array_push(x_93, x_24);
x_95 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addTraceAsMessages___spec__2(x_27, x_91);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_74, x_96);
lean_dec(x_74);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_27);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_91);
x_99 = lean_array_uset(x_75, x_90, x_98);
x_100 = lean_unsigned_to_nat(4u);
x_101 = lean_nat_mul(x_97, x_100);
x_102 = lean_unsigned_to_nat(3u);
x_103 = lean_nat_div(x_101, x_102);
lean_dec(x_101);
x_104 = lean_array_get_size(x_99);
x_105 = lean_nat_dec_le(x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; 
x_106 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addTraceAsMessages___spec__3(x_99);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_106);
lean_inc(x_6);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_6);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_usize_add(x_9, x_88);
x_9 = x_109;
x_10 = x_108;
goto _start;
}
else
{
lean_object* x_111; lean_object* x_112; size_t x_113; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_97);
lean_ctor_set(x_111, 1, x_99);
lean_inc(x_6);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_6);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_usize_add(x_9, x_88);
x_9 = x_113;
x_10 = x_112;
goto _start;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; size_t x_120; 
lean_inc(x_3);
x_115 = lean_array_uset(x_75, x_90, x_3);
x_116 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addTraceAsMessages___spec__7(x_27, x_94, x_91);
x_117 = lean_array_uset(x_115, x_90, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_74);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_6);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_6);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_usize_add(x_9, x_88);
x_9 = x_120;
x_10 = x_119;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_array_size(x_10);
x_15 = 0;
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__9(x_1, x_2, x_3, x_4, x_10, x_11, x_12, x_10, x_14, x_15, x_13, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8___lambda__1(x_20, x_21, x_7, x_8, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
x_33 = lean_array_size(x_29);
x_34 = 0;
x_35 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__10(x_1, x_2, x_3, x_29, x_30, x_31, x_29, x_33, x_34, x_32, x_7, x_8, x_9);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
x_41 = l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8___lambda__1(x_39, x_40, x_7, x_8, x_38);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_36);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_9, x_8);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_array_uget(x_7, x_9);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 5);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Lean_Syntax_getPos_x3f(x_20, x_21);
x_23 = l_Lean_Syntax_getTailPos_x3f(x_20, x_21);
lean_dec(x_20);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_125; 
x_125 = lean_unsigned_to_nat(0u);
x_25 = x_125;
goto block_124;
}
else
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_22, 0);
lean_inc(x_126);
lean_dec(x_22);
x_25 = x_126;
goto block_124;
}
block_124:
{
lean_object* x_26; 
if (lean_obj_tag(x_23) == 0)
{
lean_inc(x_25);
x_26 = x_25;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_23, 0);
lean_inc(x_123);
lean_dec(x_23);
x_26 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_26);
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
x_31 = lean_array_get_size(x_30);
x_32 = lean_uint64_of_nat(x_25);
lean_dec(x_25);
x_33 = lean_uint64_of_nat(x_26);
lean_dec(x_26);
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
x_46 = lean_array_uget(x_30, x_45);
x_47 = l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
x_48 = l_Std_DHashMap_Internal_AssocList_getD___at_Lean_addTraceAsMessages___spec__1(x_27, x_47, x_46);
x_49 = lean_array_push(x_48, x_24);
x_50 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addTraceAsMessages___spec__2(x_27, x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_29, x_51);
lean_dec(x_29);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_27);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_46);
x_54 = lean_array_uset(x_30, x_45, x_53);
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_nat_mul(x_52, x_55);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_nat_div(x_56, x_57);
lean_dec(x_56);
x_59 = lean_array_get_size(x_54);
x_60 = lean_nat_dec_le(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; size_t x_63; 
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addTraceAsMessages___spec__3(x_54);
lean_ctor_set(x_17, 1, x_61);
lean_ctor_set(x_17, 0, x_52);
lean_inc(x_6);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_6);
lean_ctor_set(x_62, 1, x_17);
x_63 = lean_usize_add(x_9, x_43);
x_9 = x_63;
x_10 = x_62;
goto _start;
}
else
{
lean_object* x_65; size_t x_66; 
lean_ctor_set(x_17, 1, x_54);
lean_ctor_set(x_17, 0, x_52);
lean_inc(x_6);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_17);
x_66 = lean_usize_add(x_9, x_43);
x_9 = x_66;
x_10 = x_65;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; 
lean_inc(x_3);
x_68 = lean_array_uset(x_30, x_45, x_3);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addTraceAsMessages___spec__7(x_27, x_49, x_46);
x_70 = lean_array_uset(x_68, x_45, x_69);
lean_ctor_set(x_17, 1, x_70);
lean_inc(x_6);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_6);
lean_ctor_set(x_71, 1, x_17);
x_72 = lean_usize_add(x_9, x_43);
x_9 = x_72;
x_10 = x_71;
goto _start;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_74 = lean_ctor_get(x_17, 0);
x_75 = lean_ctor_get(x_17, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_17);
x_76 = lean_array_get_size(x_75);
x_77 = lean_uint64_of_nat(x_25);
lean_dec(x_25);
x_78 = lean_uint64_of_nat(x_26);
lean_dec(x_26);
x_79 = lean_uint64_mix_hash(x_77, x_78);
x_80 = 32;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = 16;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_uint64_xor(x_82, x_84);
x_86 = lean_uint64_to_usize(x_85);
x_87 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_88 = 1;
x_89 = lean_usize_sub(x_87, x_88);
x_90 = lean_usize_land(x_86, x_89);
x_91 = lean_array_uget(x_75, x_90);
x_92 = l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
x_93 = l_Std_DHashMap_Internal_AssocList_getD___at_Lean_addTraceAsMessages___spec__1(x_27, x_92, x_91);
x_94 = lean_array_push(x_93, x_24);
x_95 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addTraceAsMessages___spec__2(x_27, x_91);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_74, x_96);
lean_dec(x_74);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_27);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_91);
x_99 = lean_array_uset(x_75, x_90, x_98);
x_100 = lean_unsigned_to_nat(4u);
x_101 = lean_nat_mul(x_97, x_100);
x_102 = lean_unsigned_to_nat(3u);
x_103 = lean_nat_div(x_101, x_102);
lean_dec(x_101);
x_104 = lean_array_get_size(x_99);
x_105 = lean_nat_dec_le(x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; 
x_106 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addTraceAsMessages___spec__3(x_99);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_106);
lean_inc(x_6);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_6);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_usize_add(x_9, x_88);
x_9 = x_109;
x_10 = x_108;
goto _start;
}
else
{
lean_object* x_111; lean_object* x_112; size_t x_113; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_97);
lean_ctor_set(x_111, 1, x_99);
lean_inc(x_6);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_6);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_usize_add(x_9, x_88);
x_9 = x_113;
x_10 = x_112;
goto _start;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; size_t x_120; 
lean_inc(x_3);
x_115 = lean_array_uset(x_75, x_90, x_3);
x_116 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addTraceAsMessages___spec__7(x_27, x_94, x_91);
x_117 = lean_array_uset(x_115, x_90, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_74);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_6);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_6);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_usize_add(x_9, x_88);
x_9 = x_120;
x_10 = x_119;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_inc(x_3);
x_10 = l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8(x_1, x_2, x_3, x_5, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_box(0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_array_size(x_21);
x_25 = 0;
x_26 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__11(x_1, x_2, x_3, x_20, x_21, x_22, x_21, x_24, x_25, x_23, x_6, x_7, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_FileMap_toPosition(x_1, x_2);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_3, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
lean_inc(x_17);
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
x_20 = 0;
x_21 = 0;
x_22 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
lean_ctor_set(x_3, 4, x_19);
lean_ctor_set(x_3, 3, x_22);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_5);
lean_ctor_set_uint8(x_3, sizeof(void*)*5, x_20);
lean_ctor_set_uint8(x_3, sizeof(void*)*5 + 1, x_21);
lean_ctor_set_uint8(x_3, sizeof(void*)*5 + 2, x_20);
x_23 = lean_st_ref_take(x_8, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 5);
x_28 = l_Lean_MessageLog_add(x_3, x_27);
lean_ctor_set(x_24, 5, x_28);
x_29 = lean_st_ref_set(x_8, x_24, x_25);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
x_38 = lean_ctor_get(x_24, 2);
x_39 = lean_ctor_get(x_24, 3);
x_40 = lean_ctor_get(x_24, 4);
x_41 = lean_ctor_get(x_24, 5);
x_42 = lean_ctor_get(x_24, 6);
x_43 = lean_ctor_get(x_24, 7);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_44 = l_Lean_MessageLog_add(x_3, x_41);
x_45 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 4, x_40);
lean_ctor_set(x_45, 5, x_44);
lean_ctor_set(x_45, 6, x_42);
lean_ctor_set(x_45, 7, x_43);
x_46 = lean_st_ref_set(x_8, x_45, x_25);
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
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_51 = lean_ctor_get(x_3, 2);
lean_inc(x_51);
lean_dec(x_3);
x_52 = lean_ctor_get(x_7, 6);
x_53 = lean_ctor_get(x_7, 7);
lean_inc(x_53);
lean_inc(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_4);
x_56 = 0;
x_57 = 0;
x_58 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_59 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_10);
lean_ctor_set(x_59, 2, x_51);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_59, 4, x_55);
lean_ctor_set_uint8(x_59, sizeof(void*)*5, x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*5 + 1, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*5 + 2, x_56);
x_60 = lean_st_ref_take(x_8, x_9);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 6);
lean_inc(x_69);
x_70 = lean_ctor_get(x_61, 7);
lean_inc(x_70);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 lean_ctor_release(x_61, 6);
 lean_ctor_release(x_61, 7);
 x_71 = x_61;
} else {
 lean_dec_ref(x_61);
 x_71 = lean_box(0);
}
x_72 = l_Lean_MessageLog_add(x_59, x_68);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 8, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_65);
lean_ctor_set(x_73, 3, x_66);
lean_ctor_set(x_73, 4, x_67);
lean_ctor_set(x_73, 5, x_72);
lean_ctor_set(x_73, 6, x_69);
lean_ctor_set(x_73, 7, x_70);
x_74 = lean_st_ref_set(x_8, x_73, x_62);
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
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_instMonadLogCoreM___lambda__5___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__2() {
_start:
{
lean_object* x_1; double x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___closed__1;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_6);
x_12 = lean_array_uget(x_3, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__2;
x_19 = l_Lean_MessageData_nil;
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_14);
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__1;
lean_ctor_set_tag(x_13, 8);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_21);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_25 = 0;
lean_inc(x_13);
lean_inc(x_23);
lean_inc(x_22);
x_26 = l_Lean_Elab_mkMessageCore(x_22, x_23, x_13, x_25, x_16, x_17);
lean_dec(x_17);
if (x_24 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_box(0);
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___lambda__1(x_23, x_16, x_26, x_13, x_22, x_27, x_7, x_8, x_9);
lean_dec(x_16);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
x_6 = x_27;
x_9 = x_29;
goto _start;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_13);
x_34 = l_Lean_MessageData_hasTag(x_33, x_13);
if (x_34 == 0)
{
size_t x_35; size_t x_36; lean_object* x_37; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_16);
x_35 = 1;
x_36 = lean_usize_add(x_5, x_35);
x_37 = lean_box(0);
x_5 = x_36;
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
x_39 = lean_box(0);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___lambda__1(x_23, x_16, x_26, x_13, x_22, x_39, x_7, x_8, x_9);
lean_dec(x_16);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = 1;
x_43 = lean_usize_add(x_5, x_42);
x_5 = x_43;
x_6 = x_39;
x_9 = x_41;
goto _start;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; 
x_45 = lean_ctor_get(x_13, 0);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_13);
x_47 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__2;
x_48 = l_Lean_MessageData_nil;
x_49 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_14);
x_50 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__1;
x_51 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_ctor_get(x_7, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_55 = 0;
lean_inc(x_51);
lean_inc(x_53);
lean_inc(x_52);
x_56 = l_Lean_Elab_mkMessageCore(x_52, x_53, x_51, x_55, x_45, x_46);
lean_dec(x_46);
if (x_54 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; 
x_57 = lean_box(0);
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___lambda__1(x_53, x_45, x_56, x_51, x_52, x_57, x_7, x_8, x_9);
lean_dec(x_45);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = 1;
x_61 = lean_usize_add(x_5, x_60);
x_5 = x_61;
x_6 = x_57;
x_9 = x_59;
goto _start;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_51);
x_64 = l_Lean_MessageData_hasTag(x_63, x_51);
if (x_64 == 0)
{
size_t x_65; size_t x_66; lean_object* x_67; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_45);
x_65 = 1;
x_66 = lean_usize_add(x_5, x_65);
x_67 = lean_box(0);
x_5 = x_66;
x_6 = x_67;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; 
x_69 = lean_box(0);
x_70 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___lambda__1(x_53, x_45, x_56, x_51, x_52, x_69, x_7, x_8, x_9);
lean_dec(x_45);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = 1;
x_73 = lean_usize_add(x_5, x_72);
x_5 = x_73;
x_6 = x_69;
x_9 = x_71;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqPos___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instHashablePos___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__4;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__6;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_30; 
x_6 = lean_box(0);
x_7 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__3;
x_8 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__5;
x_9 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__8;
x_10 = l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7(x_7, x_8, x_6, x_1, x_9, x_3, x_4, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
x_19 = lean_box(0);
x_20 = 0;
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_15);
x_30 = x_14;
goto block_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_16, x_16);
if (x_39 == 0)
{
lean_dec(x_16);
lean_dec(x_15);
x_30 = x_14;
goto block_38;
}
else
{
size_t x_40; lean_object* x_41; 
x_40 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_addTraceAsMessages___spec__16(x_15, x_20, x_40, x_14);
lean_dec(x_15);
x_30 = x_41;
goto block_38;
}
}
block_29:
{
size_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_array_size(x_21);
x_23 = lean_box(0);
x_24 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12(x_19, x_21, x_21, x_22, x_20, x_23, x_3, x_4, x_12);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
block_38:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_array_get_size(x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_31, x_32);
x_34 = lean_nat_dec_eq(x_31, x_17);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_17, x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_inc(x_33);
x_36 = l_Array_qsort_sort___at_Lean_addTraceAsMessages___spec__15(x_31, x_30, x_33, x_33, lean_box(0), lean_box(0));
lean_dec(x_33);
lean_dec(x_31);
x_21 = x_36;
goto block_29;
}
else
{
lean_object* x_37; 
x_37 = l_Array_qsort_sort___at_Lean_addTraceAsMessages___spec__15(x_31, x_30, x_17, x_33, lean_box(0), lean_box(0));
lean_dec(x_33);
lean_dec(x_31);
x_21 = x_37;
goto block_29;
}
}
else
{
lean_dec(x_33);
lean_dec(x_31);
x_21 = x_30;
goto block_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_PersistentArray_isEmpty___rarg(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_free_object(x_5);
x_10 = lean_box(0);
x_11 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1(x_7, x_10, x_2, x_3, x_8);
lean_dec(x_7);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_2);
x_12 = lean_box(0);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = l_Lean_PersistentArray_isEmpty___rarg(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1(x_13, x_16, x_2, x_3, x_14);
lean_dec(x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_output;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__1;
x_6 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__2;
x_7 = l_Lean_Option_get_x3f___at_Lean_addTraceAsMessages___spec__17(x_4, x_6);
lean_dec(x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_apply_4(x_5, x_8, x_1, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_8, 6);
x_12 = lean_ctor_get(x_8, 7);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = 0;
x_16 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_17 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_5);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 2, x_6);
x_18 = lean_st_ref_take(x_9, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_19, 5);
x_23 = l_Lean_MessageLog_add(x_17, x_22);
lean_ctor_set(x_19, 5, x_23);
x_24 = lean_st_ref_set(x_9, x_19, x_20);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
x_33 = lean_ctor_get(x_19, 2);
x_34 = lean_ctor_get(x_19, 3);
x_35 = lean_ctor_get(x_19, 4);
x_36 = lean_ctor_get(x_19, 5);
x_37 = lean_ctor_get(x_19, 6);
x_38 = lean_ctor_get(x_19, 7);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_39 = l_Lean_MessageLog_add(x_17, x_36);
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_37);
lean_ctor_set(x_40, 7, x_38);
x_41 = lean_st_ref_set(x_9, x_40, x_20);
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
static lean_object* _init_l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_183; uint8_t x_184; 
x_183 = 2;
x_184 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_183);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_box(0);
x_8 = x_185;
goto block_182;
}
else
{
lean_object* x_186; uint8_t x_187; 
lean_inc(x_2);
x_186 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_box(0);
x_8 = x_188;
goto block_182;
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_5);
lean_dec(x_2);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_7);
return x_190;
}
}
block_182:
{
uint8_t x_9; lean_object* x_176; uint8_t x_177; uint8_t x_178; 
lean_dec(x_8);
x_176 = lean_ctor_get(x_5, 2);
lean_inc(x_176);
x_177 = 1;
x_178 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_177);
if (x_178 == 0)
{
lean_dec(x_176);
x_9 = x_3;
goto block_175;
}
else
{
lean_object* x_179; uint8_t x_180; 
x_179 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___closed__1;
x_180 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_176, x_179);
lean_dec(x_176);
if (x_180 == 0)
{
x_9 = x_3;
goto block_175;
}
else
{
uint8_t x_181; 
x_181 = 2;
x_9 = x_181;
goto block_175;
}
}
block_175:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 5);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_14 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
x_15 = 0;
x_16 = l_Lean_Syntax_getPos_x3f(x_14, x_15);
x_17 = l_Lean_Syntax_getTailPos_x3f(x_14, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_FileMap_toPosition(x_11, x_22);
lean_inc(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
if (x_13 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_18);
x_25 = lean_box(0);
x_26 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_20, x_10, x_23, x_24, x_9, x_4, x_25, x_5, x_6, x_21);
lean_dec(x_5);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_20);
x_28 = l_Lean_MessageData_hasTag(x_27, x_20);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_5);
x_29 = lean_box(0);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_18);
x_30 = lean_box(0);
x_31 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_20, x_10, x_23, x_24, x_9, x_4, x_30, x_5, x_6, x_21);
lean_dec(x_5);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_FileMap_toPosition(x_11, x_34);
lean_inc(x_35);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
if (x_13 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_32, x_10, x_35, x_36, x_9, x_4, x_37, x_5, x_6, x_33);
lean_dec(x_5);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_32);
x_40 = l_Lean_MessageData_hasTag(x_39, x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_5);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_32, x_10, x_35, x_36, x_9, x_4, x_43, x_5, x_6, x_33);
lean_dec(x_5);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_52 = l_Lean_FileMap_toPosition(x_11, x_51);
x_53 = l_Lean_FileMap_toPosition(x_11, x_46);
lean_dec(x_46);
lean_ctor_set(x_17, 0, x_53);
if (x_13 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_free_object(x_47);
x_54 = lean_box(0);
x_55 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_49, x_10, x_52, x_17, x_9, x_4, x_54, x_5, x_6, x_50);
lean_dec(x_5);
return x_55;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_49);
x_57 = l_Lean_MessageData_hasTag(x_56, x_49);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_17);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_10);
lean_dec(x_5);
x_58 = lean_box(0);
lean_ctor_set(x_47, 0, x_58);
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_47);
x_59 = lean_box(0);
x_60 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_49, x_10, x_52, x_17, x_9, x_4, x_59, x_5, x_6, x_50);
lean_dec(x_5);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_64 = l_Lean_FileMap_toPosition(x_11, x_63);
x_65 = l_Lean_FileMap_toPosition(x_11, x_46);
lean_dec(x_46);
lean_ctor_set(x_17, 0, x_65);
if (x_13 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_61, x_10, x_64, x_17, x_9, x_4, x_66, x_5, x_6, x_62);
lean_dec(x_5);
return x_67;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_61);
x_69 = l_Lean_MessageData_hasTag(x_68, x_61);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_17);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_10);
lean_dec(x_5);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
x_73 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_61, x_10, x_64, x_17, x_9, x_4, x_72, x_5, x_6, x_62);
lean_dec(x_5);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_74 = lean_ctor_get(x_17, 0);
lean_inc(x_74);
lean_dec(x_17);
x_75 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_80 = l_Lean_FileMap_toPosition(x_11, x_79);
x_81 = l_Lean_FileMap_toPosition(x_11, x_74);
lean_dec(x_74);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (x_13 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_76, x_10, x_80, x_82, x_9, x_4, x_83, x_5, x_6, x_77);
lean_dec(x_5);
return x_84;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_76);
x_86 = l_Lean_MessageData_hasTag(x_85, x_76);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_10);
lean_dec(x_5);
x_87 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_78;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_78);
x_89 = lean_box(0);
x_90 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_76, x_10, x_80, x_82, x_9, x_4, x_89, x_5, x_6, x_77);
lean_dec(x_5);
return x_90;
}
}
}
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_16);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_16, 0);
x_93 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
x_97 = l_Lean_FileMap_toPosition(x_11, x_92);
lean_dec(x_92);
lean_inc(x_97);
lean_ctor_set(x_16, 0, x_97);
if (x_13 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_free_object(x_93);
x_98 = lean_box(0);
x_99 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_95, x_10, x_97, x_16, x_9, x_4, x_98, x_5, x_6, x_96);
lean_dec(x_5);
return x_99;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_95);
x_101 = l_Lean_MessageData_hasTag(x_100, x_95);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_16);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_10);
lean_dec(x_5);
x_102 = lean_box(0);
lean_ctor_set(x_93, 0, x_102);
return x_93;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_free_object(x_93);
x_103 = lean_box(0);
x_104 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_95, x_10, x_97, x_16, x_9, x_4, x_103, x_5, x_6, x_96);
lean_dec(x_5);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_93, 0);
x_106 = lean_ctor_get(x_93, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_93);
x_107 = l_Lean_FileMap_toPosition(x_11, x_92);
lean_dec(x_92);
lean_inc(x_107);
lean_ctor_set(x_16, 0, x_107);
if (x_13 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_box(0);
x_109 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_105, x_10, x_107, x_16, x_9, x_4, x_108, x_5, x_6, x_106);
lean_dec(x_5);
return x_109;
}
else
{
lean_object* x_110; uint8_t x_111; 
x_110 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_105);
x_111 = l_Lean_MessageData_hasTag(x_110, x_105);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_16);
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_10);
lean_dec(x_5);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_106);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_box(0);
x_115 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_105, x_10, x_107, x_16, x_9, x_4, x_114, x_5, x_6, x_106);
lean_dec(x_5);
return x_115;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_16, 0);
lean_inc(x_116);
lean_dec(x_16);
x_117 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = l_Lean_FileMap_toPosition(x_11, x_116);
lean_dec(x_116);
lean_inc(x_121);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
if (x_13 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_120);
x_123 = lean_box(0);
x_124 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_118, x_10, x_121, x_122, x_9, x_4, x_123, x_5, x_6, x_119);
lean_dec(x_5);
return x_124;
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_118);
x_126 = l_Lean_MessageData_hasTag(x_125, x_118);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_5);
x_127 = lean_box(0);
if (lean_is_scalar(x_120)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_120;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_119);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_120);
x_129 = lean_box(0);
x_130 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_118, x_10, x_121, x_122, x_9, x_4, x_129, x_5, x_6, x_119);
lean_dec(x_5);
return x_130;
}
}
}
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_16, 0);
lean_inc(x_131);
lean_dec(x_16);
x_132 = !lean_is_exclusive(x_17);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_17, 0);
x_134 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_11);
x_138 = l_Lean_FileMap_toPosition(x_11, x_131);
lean_dec(x_131);
x_139 = l_Lean_FileMap_toPosition(x_11, x_133);
lean_dec(x_133);
lean_ctor_set(x_17, 0, x_139);
if (x_13 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_free_object(x_134);
x_140 = lean_box(0);
x_141 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_136, x_10, x_138, x_17, x_9, x_4, x_140, x_5, x_6, x_137);
lean_dec(x_5);
return x_141;
}
else
{
lean_object* x_142; uint8_t x_143; 
x_142 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_136);
x_143 = l_Lean_MessageData_hasTag(x_142, x_136);
if (x_143 == 0)
{
lean_object* x_144; 
lean_dec(x_17);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_10);
lean_dec(x_5);
x_144 = lean_box(0);
lean_ctor_set(x_134, 0, x_144);
return x_134;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_free_object(x_134);
x_145 = lean_box(0);
x_146 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_136, x_10, x_138, x_17, x_9, x_4, x_145, x_5, x_6, x_137);
lean_dec(x_5);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_134, 0);
x_148 = lean_ctor_get(x_134, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_134);
lean_inc(x_11);
x_149 = l_Lean_FileMap_toPosition(x_11, x_131);
lean_dec(x_131);
x_150 = l_Lean_FileMap_toPosition(x_11, x_133);
lean_dec(x_133);
lean_ctor_set(x_17, 0, x_150);
if (x_13 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_box(0);
x_152 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_147, x_10, x_149, x_17, x_9, x_4, x_151, x_5, x_6, x_148);
lean_dec(x_5);
return x_152;
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_147);
x_154 = l_Lean_MessageData_hasTag(x_153, x_147);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_17);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_5);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_148);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_box(0);
x_158 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_147, x_10, x_149, x_17, x_9, x_4, x_157, x_5, x_6, x_148);
lean_dec(x_5);
return x_158;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_159 = lean_ctor_get(x_17, 0);
lean_inc(x_159);
lean_dec(x_17);
x_160 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
lean_inc(x_11);
x_164 = l_Lean_FileMap_toPosition(x_11, x_131);
lean_dec(x_131);
x_165 = l_Lean_FileMap_toPosition(x_11, x_159);
lean_dec(x_159);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
if (x_13 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_163);
x_167 = lean_box(0);
x_168 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_161, x_10, x_164, x_166, x_9, x_4, x_167, x_5, x_6, x_162);
lean_dec(x_5);
return x_168;
}
else
{
lean_object* x_169; uint8_t x_170; 
x_169 = l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1;
lean_inc(x_161);
x_170 = l_Lean_MessageData_hasTag(x_169, x_161);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_10);
lean_dec(x_5);
x_171 = lean_box(0);
if (lean_is_scalar(x_163)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_163;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_162);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_163);
x_173 = lean_box(0);
x_174 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_161, x_10, x_164, x_166, x_9, x_4, x_173, x_5, x_6, x_162);
lean_dec(x_5);
return x_174;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 5);
lean_inc(x_6);
x_7 = 0;
x_8 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14(x_6, x_1, x_2, x_7, x_3, x_4, x_5);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_Core_wrapAsyncAsSnapshot___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_get_set_stdout(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_get_set_stdout(x_7, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_get_set_stdout(x_7, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_Core_wrapAsyncAsSnapshot___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_get_set_stdin(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_get_set_stdin(x_7, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_get_set_stdin(x_7, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_Core_wrapAsyncAsSnapshot___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_get_set_stderr(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_get_set_stderr(x_7, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_get_set_stderr(x_7, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__3;
x_3 = lean_unsigned_to_nat(128u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__1;
x_7 = lean_st_mk_ref(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_mk_ref(x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_IO_FS_Stream_ofBuffer(x_8);
lean_inc(x_12);
x_15 = l_IO_FS_Stream_ofBuffer(x_12);
if (x_2 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_Core_wrapAsyncAsSnapshot___spec__16), 5, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_1);
x_17 = l_IO_withStdin___at_Lean_Core_wrapAsyncAsSnapshot___spec__17(x_14, x_16, x_3, x_4, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_12, x_19);
lean_dec(x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_string_validate_utf8(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
x_25 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5;
x_26 = l_panic___at_Lean_Name_getString_x21___spec__1(x_25);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_26);
lean_ctor_set(x_20, 0, x_10);
return x_20;
}
else
{
lean_object* x_27; 
x_27 = lean_string_from_utf8_unchecked(x_23);
lean_dec(x_23);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_27);
lean_ctor_set(x_20, 0, x_10);
return x_20;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_string_validate_utf8(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_32 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5;
x_33 = l_panic___at_Lean_Name_getString_x21___spec__1(x_32);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_string_from_utf8_unchecked(x_30);
lean_dec(x_30);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_10);
lean_dec(x_12);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_15);
x_41 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lean_Core_wrapAsyncAsSnapshot___spec__18), 5, 2);
lean_closure_set(x_41, 0, x_15);
lean_closure_set(x_41, 1, x_1);
x_42 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_Core_wrapAsyncAsSnapshot___spec__16), 5, 2);
lean_closure_set(x_42, 0, x_15);
lean_closure_set(x_42, 1, x_41);
x_43 = l_IO_withStdin___at_Lean_Core_wrapAsyncAsSnapshot___spec__17(x_14, x_42, x_3, x_4, x_13);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_st_ref_get(x_12, x_45);
lean_dec(x_12);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_string_validate_utf8(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
x_51 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5;
x_52 = l_panic___at_Lean_Name_getString_x21___spec__1(x_51);
lean_ctor_set(x_10, 1, x_44);
lean_ctor_set(x_10, 0, x_52);
lean_ctor_set(x_46, 0, x_10);
return x_46;
}
else
{
lean_object* x_53; 
x_53 = lean_string_from_utf8_unchecked(x_49);
lean_dec(x_49);
lean_ctor_set(x_10, 1, x_44);
lean_ctor_set(x_10, 0, x_53);
lean_ctor_set(x_46, 0, x_10);
return x_46;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_string_validate_utf8(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
x_58 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5;
x_59 = l_panic___at_Lean_Name_getString_x21___spec__1(x_58);
lean_ctor_set(x_10, 1, x_44);
lean_ctor_set(x_10, 0, x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_10);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_string_from_utf8_unchecked(x_56);
lean_dec(x_56);
lean_ctor_set(x_10, 1, x_44);
lean_ctor_set(x_10, 0, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_10);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_free_object(x_10);
lean_dec(x_12);
x_63 = !lean_is_exclusive(x_43);
if (x_63 == 0)
{
return x_43;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_43, 0);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_43);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_10, 0);
x_68 = lean_ctor_get(x_10, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_10);
x_69 = l_IO_FS_Stream_ofBuffer(x_8);
lean_inc(x_67);
x_70 = l_IO_FS_Stream_ofBuffer(x_67);
if (x_2 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_Core_wrapAsyncAsSnapshot___spec__16), 5, 2);
lean_closure_set(x_71, 0, x_70);
lean_closure_set(x_71, 1, x_1);
x_72 = l_IO_withStdin___at_Lean_Core_wrapAsyncAsSnapshot___spec__17(x_69, x_71, x_3, x_4, x_68);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_st_ref_get(x_67, x_74);
lean_dec(x_67);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_string_validate_utf8(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_79);
x_81 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5;
x_82 = l_panic___at_Lean_Name_getString_x21___spec__1(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_73);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_string_from_utf8_unchecked(x_79);
lean_dec(x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_73);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_77);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_67);
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_90 = x_72;
} else {
 lean_dec_ref(x_72);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_inc(x_70);
x_92 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lean_Core_wrapAsyncAsSnapshot___spec__18), 5, 2);
lean_closure_set(x_92, 0, x_70);
lean_closure_set(x_92, 1, x_1);
x_93 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_Core_wrapAsyncAsSnapshot___spec__16), 5, 2);
lean_closure_set(x_93, 0, x_70);
lean_closure_set(x_93, 1, x_92);
x_94 = l_IO_withStdin___at_Lean_Core_wrapAsyncAsSnapshot___spec__17(x_69, x_93, x_3, x_4, x_68);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_st_ref_get(x_67, x_96);
lean_dec(x_67);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_string_validate_utf8(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_101);
x_103 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5;
x_104 = l_panic___at_Lean_Name_getString_x21___spec__1(x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
if (lean_is_scalar(x_100)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_100;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_99);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_string_from_utf8_unchecked(x_101);
lean_dec(x_101);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_95);
if (lean_is_scalar(x_100)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_100;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_99);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_67);
x_110 = lean_ctor_get(x_94, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_94, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_112 = x_94;
} else {
 lean_dec_ref(x_94);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Core_instInhabitedCache___closed__2;
x_3 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_io_get_tid(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_take(x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_14 = lean_ctor_get(x_11, 5);
x_15 = lean_ctor_get(x_11, 7);
lean_dec(x_15);
x_16 = lean_ctor_get(x_11, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_dec(x_17);
x_18 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
x_19 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unbox_uint64(x_8);
lean_dec(x_8);
lean_ctor_set_uint64(x_19, sizeof(void*)*1, x_20);
x_21 = l_Lean_MessageLog_markAllReported(x_14);
x_22 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2___closed__1;
x_23 = l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
lean_ctor_set(x_11, 7, x_23);
lean_ctor_set(x_11, 6, x_22);
lean_ctor_set(x_11, 5, x_21);
lean_ctor_set(x_11, 3, x_19);
x_24 = lean_st_ref_set(x_5, x_11, x_12);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_26, 0, x_1);
x_27 = lean_apply_1(x_2, x_3);
x_35 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__3;
x_36 = 1;
x_37 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1(x_35, x_26, x_27, x_36, x_37, x_4, x_5, x_25);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_5);
x_40 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6(x_4, x_5, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_28 = x_41;
goto block_34;
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_40);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = l_Lean_Exception_isInterrupt(x_46);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = l_Lean_Exception_toMessageData(x_46);
x_50 = 2;
lean_inc(x_4);
x_51 = l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(x_49, x_50, x_4, x_5, x_47);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_5);
x_53 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6(x_4, x_5, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_28 = x_54;
goto block_34;
}
else
{
uint8_t x_55; 
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_53);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_46);
lean_inc(x_5);
x_59 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6(x_4, x_5, x_47);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_28 = x_60;
goto block_34;
}
else
{
uint8_t x_61; 
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_59);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
block_34:
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_st_ref_get(x_5, x_28);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_65 = lean_ctor_get(x_11, 0);
x_66 = lean_ctor_get(x_11, 1);
x_67 = lean_ctor_get(x_11, 2);
x_68 = lean_ctor_get(x_11, 4);
x_69 = lean_ctor_get(x_11, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_11);
x_70 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
x_71 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_unbox_uint64(x_8);
lean_dec(x_8);
lean_ctor_set_uint64(x_71, sizeof(void*)*1, x_72);
x_73 = l_Lean_MessageLog_markAllReported(x_69);
x_74 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2___closed__1;
x_75 = l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
x_76 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_66);
lean_ctor_set(x_76, 2, x_67);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_76, 4, x_68);
lean_ctor_set(x_76, 5, x_73);
lean_ctor_set(x_76, 6, x_74);
lean_ctor_set(x_76, 7, x_75);
x_77 = lean_st_ref_set(x_5, x_76, x_12);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_79, 0, x_1);
x_80 = lean_apply_1(x_2, x_3);
x_88 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__3;
x_89 = 1;
x_90 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
lean_inc(x_5);
lean_inc(x_4);
x_91 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1(x_88, x_79, x_80, x_89, x_90, x_4, x_5, x_78);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_5);
x_93 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6(x_4, x_5, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_81 = x_94;
goto block_87;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_5);
x_95 = lean_ctor_get(x_93, 0);
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
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_91, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_91, 1);
lean_inc(x_100);
lean_dec(x_91);
x_101 = l_Lean_Exception_isInterrupt(x_99);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = l_Lean_Exception_toMessageData(x_99);
x_103 = 2;
lean_inc(x_4);
x_104 = l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(x_102, x_103, x_4, x_5, x_100);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
lean_inc(x_5);
x_106 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6(x_4, x_5, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_81 = x_107;
goto block_87;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_5);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_99);
lean_inc(x_5);
x_112 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6(x_4, x_5, x_100);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_81 = x_113;
goto block_87;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_5);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
block_87:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_st_ref_get(x_5, x_81);
lean_dec(x_5);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_stderrAsMessages;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2), 6, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
x_9 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__3___closed__1;
x_10 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_9);
lean_dec(x_7);
x_11 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15(x_8, x_10, x_4, x_5, x_6);
return x_11;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__1;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__2;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__3;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__6() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__7() {
_start:
{
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__6;
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__3;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_3 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__5;
x_4 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__7;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__8;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_15; 
x_15 = lean_apply_2(x_1, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_6 = x_18;
x_7 = x_17;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_6 = x_21;
x_7 = x_20;
goto block_14;
}
block_14:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__9;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Core_mkSnapshot(x_11, x_2, x_12, x_3, x_7);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__3), 6, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_1);
lean_inc(x_4);
x_8 = l_Lean_Core_wrapAsync___rarg(x_7, x_2, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4), 5, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_3);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4), 5, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_MonadExcept_ofExcept___at_Lean_Core_wrapAsyncAsSnapshot___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = lean_unbox_float(x_8);
lean_dec(x_8);
x_17 = lean_unbox_float(x_9);
lean_dec(x_9);
x_18 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2(x_1, x_14, x_3, x_4, x_5, x_6, x_15, x_16, x_17, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox_float(x_7);
lean_dec(x_7);
x_17 = lean_unbox_float(x_8);
lean_dec(x_8);
x_18 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_16 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15, x_16, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_15, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forInAux___at_Lean_Core_wrapAsyncAsSnapshot___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_15, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forIn___at_Lean_Core_wrapAsyncAsSnapshot___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___lambda__1(x_1, x_2, x_3, x_4, x_11, x_12, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsyncAsSnapshot___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_4, 4);
x_9 = lean_nat_dec_le(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_ctor_set(x_4, 4, x_1);
x_10 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 4);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
x_19 = lean_ctor_get(x_4, 7);
x_20 = lean_ctor_get(x_4, 8);
x_21 = lean_ctor_get(x_4, 9);
x_22 = lean_ctor_get(x_4, 10);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_24 = lean_ctor_get(x_4, 11);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_26 = lean_ctor_get(x_4, 12);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_27 = lean_nat_dec_le(x_1, x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_13);
lean_ctor_set(x_28, 2, x_14);
lean_ctor_set(x_28, 3, x_15);
lean_ctor_set(x_28, 4, x_1);
lean_ctor_set(x_28, 5, x_17);
lean_ctor_set(x_28, 6, x_18);
lean_ctor_set(x_28, 7, x_19);
lean_ctor_set(x_28, 8, x_20);
lean_ctor_set(x_28, 9, x_21);
lean_ctor_set(x_28, 10, x_22);
lean_ctor_set(x_28, 11, x_24);
lean_ctor_set(x_28, 12, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*13, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 1, x_25);
x_29 = lean_apply_3(x_3, x_28, x_5, x_6);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_13);
lean_ctor_set(x_30, 2, x_14);
lean_ctor_set(x_30, 3, x_15);
lean_ctor_set(x_30, 4, x_16);
lean_ctor_set(x_30, 5, x_17);
lean_ctor_set(x_30, 6, x_18);
lean_ctor_set(x_30, 7, x_19);
lean_ctor_set(x_30, 8, x_20);
lean_ctor_set(x_30, 9, x_21);
lean_ctor_set(x_30, 10, x_22);
lean_ctor_set(x_30, 11, x_24);
lean_ctor_set(x_30, 12, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*13, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*13 + 1, x_25);
x_31 = lean_apply_3(x_3, x_30, x_5, x_6);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_withAtLeastMaxRecDepth___rarg___lambda__1), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_3(x_1, lean_box(0), x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_withAtLeastMaxRecDepth___rarg), 3, 0);
return x_3;
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
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__1;
x_12 = lean_string_dec_eq(x_6, x_11);
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
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
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
static lean_object* _init_l_Lean_mkArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_mkArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkArrow___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_mkArrow___closed__2;
x_7 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_6, x_3, x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = 0;
x_11 = l_Lean_Expr_forallE___override(x_9, x_1, x_2, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = 0;
x_15 = l_Lean_Expr_forallE___override(x_12, x_1, x_2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
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
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkArrowN___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = 1;
x_10 = lean_usize_sub(x_2, x_9);
x_11 = lean_array_uget(x_1, x_10);
x_12 = l_Lean_mkArrow(x_11, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_2 = x_10;
x_4 = x_13;
x_7 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
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
x_12 = l_Array_foldrMUnsafe_fold___at_Lean_mkArrowN___spec__1(x_1, x_10, x_11, x_2, x_3, x_4, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkArrowN___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldrMUnsafe_fold___at_Lean_mkArrowN___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
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
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Empty", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrec", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recOn", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesOn", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3;
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__29;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_is_aux_recursor(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_inc(x_3);
x_5 = l_Lean_isRecCore(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_8 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_7, x_3);
lean_dec(x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_casesOnSuffix;
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_isAuxRecursorWithSuffix(x_1, x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_13 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_14 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_13, x_3);
lean_dec(x_3);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_inc(x_3);
x_17 = l_Lean_isRecCore(x_1, x_3);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = 0;
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_20 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_19, x_3);
lean_dec(x_3);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = 0;
return x_23;
}
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_find_expr(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_MessageData_ofName(x_13);
x_15 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___rarg(x_3, x_4, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_4);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_apply_2(x_21, lean_box(0), x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_3);
x_16 = lean_find_expr(x_15, x_14);
lean_dec(x_14);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_1);
lean_closure_set(x_17, 3, x_2);
lean_inc(x_2);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__3), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_5);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
lean_inc(x_12);
x_23 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_22, x_17);
x_24 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_23, x_18);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_MessageData_ofName(x_26);
x_28 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_28);
x_29 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___rarg(x_1, x_2, x_30);
lean_inc(x_12);
x_32 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_31, x_17);
x_33 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_32, x_18);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_25);
lean_free_object(x_5);
lean_dec(x_2);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_apply_2(x_35, lean_box(0), x_36);
lean_inc(x_12);
x_38 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_37, x_17);
x_39 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_38, x_18);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_3);
x_45 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_45, 0, x_3);
x_46 = lean_find_expr(x_45, x_44);
lean_dec(x_44);
lean_inc(x_2);
lean_inc(x_1);
x_47 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_47, 0, x_40);
lean_closure_set(x_47, 1, x_45);
lean_closure_set(x_47, 2, x_1);
lean_closure_set(x_47, 3, x_2);
lean_inc(x_2);
lean_inc(x_1);
x_48 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__3), 5, 4);
lean_closure_set(x_48, 0, x_1);
lean_closure_set(x_48, 1, x_2);
lean_closure_set(x_48, 2, x_3);
lean_closure_set(x_48, 3, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(0);
x_52 = lean_apply_2(x_50, lean_box(0), x_51);
lean_inc(x_42);
x_53 = lean_apply_4(x_42, lean_box(0), lean_box(0), x_52, x_47);
x_54 = lean_apply_4(x_42, lean_box(0), lean_box(0), x_53, x_48);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
lean_dec(x_46);
if (lean_obj_tag(x_55) == 4)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_MessageData_ofName(x_56);
x_58 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_throwError___rarg(x_1, x_2, x_61);
lean_inc(x_42);
x_63 = lean_apply_4(x_42, lean_box(0), lean_box(0), x_62, x_47);
x_64 = lean_apply_4(x_42, lean_box(0), lean_box(0), x_63, x_48);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_55);
lean_dec(x_2);
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
lean_dec(x_1);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_box(0);
x_68 = lean_apply_2(x_66, lean_box(0), x_67);
lean_inc(x_42);
x_69 = lean_apply_4(x_42, lean_box(0), lean_box(0), x_68, x_47);
x_70 = lean_apply_4(x_42, lean_box(0), lean_box(0), x_69, x_48);
return x_70;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_find_expr(x_3, x_13);
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3___rarg___lambda__1), 5, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_5);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
x_20 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_19, x_15);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 4)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_MessageData_ofName(x_22);
x_24 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_23);
lean_ctor_set(x_5, 0, x_24);
x_25 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___rarg(x_1, x_2, x_26);
x_28 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_27, x_15);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_21);
lean_free_object(x_5);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = lean_apply_2(x_30, lean_box(0), x_31);
x_33 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_32, x_15);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_find_expr(x_3, x_37);
lean_dec(x_37);
lean_inc(x_2);
lean_inc(x_1);
x_39 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3___rarg___lambda__1), 5, 4);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_2);
lean_closure_set(x_39, 2, x_3);
lean_closure_set(x_39, 3, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_apply_2(x_41, lean_box(0), x_42);
x_44 = lean_apply_4(x_36, lean_box(0), lean_box(0), x_43, x_39);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
if (lean_obj_tag(x_45) == 4)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_MessageData_ofName(x_46);
x_48 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___rarg(x_1, x_2, x_51);
x_53 = lean_apply_4(x_36, lean_box(0), lean_box(0), x_52, x_39);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_45);
lean_dec(x_2);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec(x_1);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = lean_apply_2(x_55, lean_box(0), x_56);
x_58 = lean_apply_4(x_36, lean_box(0), lean_box(0), x_57, x_39);
return x_58;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__3___rarg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_3);
x_15 = lean_find_expr(x_14, x_13);
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg___lambda__1), 5, 4);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_14);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg___lambda__2), 5, 4);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_5);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
lean_inc(x_12);
x_22 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_21, x_16);
x_23 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_22, x_17);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_MessageData_ofName(x_25);
x_27 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_27);
x_28 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___rarg(x_1, x_2, x_29);
lean_inc(x_12);
x_31 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_30, x_16);
x_32 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_31, x_17);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_24);
lean_free_object(x_5);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = lean_apply_2(x_34, lean_box(0), x_35);
lean_inc(x_12);
x_37 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_36, x_16);
x_38 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_37, x_17);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_3);
x_43 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_43, 0, x_3);
x_44 = lean_find_expr(x_43, x_42);
lean_dec(x_42);
lean_inc(x_2);
lean_inc(x_1);
x_45 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg___lambda__1), 5, 4);
lean_closure_set(x_45, 0, x_39);
lean_closure_set(x_45, 1, x_1);
lean_closure_set(x_45, 2, x_2);
lean_closure_set(x_45, 3, x_43);
lean_inc(x_2);
lean_inc(x_1);
x_46 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg___lambda__2), 5, 4);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_2);
lean_closure_set(x_46, 2, x_3);
lean_closure_set(x_46, 3, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_apply_2(x_48, lean_box(0), x_49);
lean_inc(x_41);
x_51 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_50, x_45);
x_52 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_51, x_46);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
if (lean_obj_tag(x_53) == 4)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_MessageData_ofName(x_54);
x_56 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___rarg(x_1, x_2, x_59);
lean_inc(x_41);
x_61 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_60, x_45);
x_62 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_61, x_46);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_53);
lean_dec(x_2);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = lean_apply_2(x_64, lean_box(0), x_65);
lean_inc(x_41);
x_67 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_66, x_45);
x_68 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_67, x_46);
return x_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_find_expr(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_MessageData_ofName(x_12);
x_14 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___rarg(x_3, x_4, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_4);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_find_expr(x_9, x_8);
lean_dec(x_8);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_MessageData_ofName(x_16);
x_18 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___rarg(x_1, x_2, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = lean_apply_2(x_24, lean_box(0), x_25);
return x_26;
}
}
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_apply_2(x_28, lean_box(0), x_5);
return x_29;
}
case 5:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
lean_dec(x_4);
x_31 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg(x_1, x_2, x_3, x_5, x_30);
return x_31;
}
case 6:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_4, 2);
lean_inc(x_32);
lean_dec(x_4);
x_33 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__4___rarg(x_1, x_2, x_3, x_5, x_32);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 2);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_39, 0, x_3);
x_40 = lean_find_expr(x_39, x_37);
lean_dec(x_37);
lean_inc(x_2);
lean_inc(x_1);
x_41 = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_36);
lean_closure_set(x_41, 2, x_1);
lean_closure_set(x_41, 3, x_2);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_apply_2(x_43, lean_box(0), x_44);
x_46 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_45, x_41);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
if (lean_obj_tag(x_47) == 4)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_MessageData_ofName(x_48);
x_50 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___rarg(x_1, x_2, x_53);
x_55 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_54, x_41);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_47);
lean_dec(x_2);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = lean_apply_2(x_57, lean_box(0), x_58);
x_60 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_59, x_41);
return x_60;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg(x_1, x_2, x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Declaration_foldExprM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("enableNew", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__1;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(compiler) enable the new code generator, this should have no significant effect on your code but it does help to test the new code generator; unset to only use the old code generator instead", 191, 191);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__1;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__1;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__3;
x_3 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__5;
x_4 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_traceBlock___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_2(x_3, x_5, x_6);
x_9 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_8, x_4, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_traceBlock___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_profileitM___at_Lean_traceBlock___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_7);
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(x_1, x_5, x_2, x_3, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__3___rarg(x_4, x_7, x_8, x_11);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_7 == 0)
{
double x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set_float(x_15, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_15, sizeof(void*)*2 + 8, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 16, x_2);
x_16 = lean_box(0);
x_17 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__1(x_4, x_5, x_10, x_6, x_15, x_16, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_8);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_2);
x_19 = lean_box(0);
x_20 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__1(x_4, x_5, x_10, x_6, x_18, x_19, x_11, x_12, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, double x_7, double x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 5);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_15 = lean_apply_4(x_9, x_5, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_16, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__2;
x_21 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_20, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_5);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_7);
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(x_1, x_5, x_2, x_3, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__5___rarg(x_4, x_7, x_8, x_11);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_7 == 0)
{
double x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set_float(x_15, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_15, sizeof(void*)*2 + 8, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 16, x_2);
x_16 = lean_box(0);
x_17 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__4(x_4, x_5, x_10, x_6, x_15, x_16, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_8);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_2);
x_19 = lean_box(0);
x_20 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__4(x_4, x_5, x_10, x_6, x_18, x_19, x_11, x_12, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, double x_7, double x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 5);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_15 = lean_apply_4(x_9, x_5, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__5(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_16, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__2;
x_21 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__5(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_20, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_5);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__7(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__1;
x_16 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_io_mono_nanos_now(x_14);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_10);
lean_inc(x_9);
x_114 = lean_apply_3(x_7, x_9, x_10, x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_119 = lean_io_mono_nanos_now(x_117);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; double x_125; double x_126; double x_127; double x_128; double x_129; lean_object* x_130; lean_object* x_131; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
x_123 = 0;
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Float_ofScientific(x_112, x_123, x_124);
lean_dec(x_112);
x_126 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_127 = lean_float_div(x_125, x_126);
x_128 = l_Float_ofScientific(x_121, x_123, x_124);
lean_dec(x_121);
x_129 = lean_float_div(x_128, x_126);
x_130 = lean_box_float(x_127);
x_131 = lean_box_float(x_129);
lean_ctor_set(x_119, 1, x_131);
lean_ctor_set(x_119, 0, x_130);
lean_ctor_set(x_114, 1, x_119);
lean_ctor_set(x_114, 0, x_118);
x_17 = x_114;
x_18 = x_122;
goto block_110;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; double x_136; double x_137; double x_138; double x_139; double x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_132 = lean_ctor_get(x_119, 0);
x_133 = lean_ctor_get(x_119, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_119);
x_134 = 0;
x_135 = lean_unsigned_to_nat(0u);
x_136 = l_Float_ofScientific(x_112, x_134, x_135);
lean_dec(x_112);
x_137 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_138 = lean_float_div(x_136, x_137);
x_139 = l_Float_ofScientific(x_132, x_134, x_135);
lean_dec(x_132);
x_140 = lean_float_div(x_139, x_137);
x_141 = lean_box_float(x_138);
x_142 = lean_box_float(x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_114, 1, x_143);
lean_ctor_set(x_114, 0, x_118);
x_17 = x_114;
x_18 = x_133;
goto block_110;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; double x_153; double x_154; double x_155; double x_156; double x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_144 = lean_ctor_get(x_114, 0);
x_145 = lean_ctor_get(x_114, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_114);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_144);
x_147 = lean_io_mono_nanos_now(x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = 0;
x_152 = lean_unsigned_to_nat(0u);
x_153 = l_Float_ofScientific(x_112, x_151, x_152);
lean_dec(x_112);
x_154 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_155 = lean_float_div(x_153, x_154);
x_156 = l_Float_ofScientific(x_148, x_151, x_152);
lean_dec(x_148);
x_157 = lean_float_div(x_156, x_154);
x_158 = lean_box_float(x_155);
x_159 = lean_box_float(x_157);
if (lean_is_scalar(x_150)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_150;
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_146);
lean_ctor_set(x_161, 1, x_160);
x_17 = x_161;
x_18 = x_149;
goto block_110;
}
}
else
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_114);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_114, 0);
x_164 = lean_ctor_get(x_114, 1);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_163);
x_166 = lean_io_mono_nanos_now(x_164);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; double x_172; double x_173; double x_174; double x_175; double x_176; lean_object* x_177; lean_object* x_178; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
x_170 = 0;
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_Float_ofScientific(x_112, x_170, x_171);
lean_dec(x_112);
x_173 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_174 = lean_float_div(x_172, x_173);
x_175 = l_Float_ofScientific(x_168, x_170, x_171);
lean_dec(x_168);
x_176 = lean_float_div(x_175, x_173);
x_177 = lean_box_float(x_174);
x_178 = lean_box_float(x_176);
lean_ctor_set(x_166, 1, x_178);
lean_ctor_set(x_166, 0, x_177);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 1, x_166);
lean_ctor_set(x_114, 0, x_165);
x_17 = x_114;
x_18 = x_169;
goto block_110;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; double x_183; double x_184; double x_185; double x_186; double x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_179 = lean_ctor_get(x_166, 0);
x_180 = lean_ctor_get(x_166, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_166);
x_181 = 0;
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Float_ofScientific(x_112, x_181, x_182);
lean_dec(x_112);
x_184 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_185 = lean_float_div(x_183, x_184);
x_186 = l_Float_ofScientific(x_179, x_181, x_182);
lean_dec(x_179);
x_187 = lean_float_div(x_186, x_184);
x_188 = lean_box_float(x_185);
x_189 = lean_box_float(x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 1, x_190);
lean_ctor_set(x_114, 0, x_165);
x_17 = x_114;
x_18 = x_180;
goto block_110;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; double x_200; double x_201; double x_202; double x_203; double x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_191 = lean_ctor_get(x_114, 0);
x_192 = lean_ctor_get(x_114, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_114);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_191);
x_194 = lean_io_mono_nanos_now(x_192);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = 0;
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Float_ofScientific(x_112, x_198, x_199);
lean_dec(x_112);
x_201 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_202 = lean_float_div(x_200, x_201);
x_203 = l_Float_ofScientific(x_195, x_198, x_199);
lean_dec(x_195);
x_204 = lean_float_div(x_203, x_201);
x_205 = lean_box_float(x_202);
x_206 = lean_box_float(x_204);
if (lean_is_scalar(x_197)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_197;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_193);
lean_ctor_set(x_208, 1, x_207);
x_17 = x_208;
x_18 = x_196;
goto block_110;
}
}
block_110:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
x_24 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_23);
if (x_24 == 0)
{
if (x_6 == 0)
{
uint8_t x_90; 
x_90 = 0;
x_25 = x_90;
goto block_89;
}
else
{
lean_object* x_91; double x_92; double x_93; lean_object* x_94; 
x_91 = lean_box(0);
x_92 = lean_unbox_float(x_21);
lean_dec(x_21);
x_93 = lean_unbox_float(x_22);
lean_dec(x_22);
x_94 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_92, x_93, x_5, x_91, x_9, x_10, x_18);
return x_94;
}
}
else
{
if (x_6 == 0)
{
double x_95; double x_96; double x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; double x_102; double x_103; double x_104; uint8_t x_105; 
x_95 = lean_unbox_float(x_22);
x_96 = lean_unbox_float(x_21);
x_97 = lean_float_sub(x_95, x_96);
x_98 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3;
x_99 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_98);
x_100 = 0;
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Float_ofScientific(x_99, x_100, x_101);
lean_dec(x_99);
x_103 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__4;
x_104 = lean_float_div(x_102, x_103);
x_105 = lean_float_decLt(x_104, x_97);
x_25 = x_105;
goto block_89;
}
else
{
lean_object* x_106; double x_107; double x_108; lean_object* x_109; 
x_106 = lean_box(0);
x_107 = lean_unbox_float(x_21);
lean_dec(x_21);
x_108 = lean_unbox_float(x_22);
lean_dec(x_22);
x_109 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_107, x_108, x_5, x_106, x_9, x_10, x_18);
return x_109;
}
}
block_89:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_st_ref_take(x_10, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 3);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = l_Lean_PersistentArray_append___rarg(x_13, x_33);
lean_dec(x_33);
lean_ctor_set(x_28, 0, x_34);
x_35 = lean_st_ref_set(x_10, x_27, x_29);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4___rarg(x_20, x_9, x_10, x_36);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
lean_dec(x_28);
x_48 = l_Lean_PersistentArray_append___rarg(x_13, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint64(x_49, sizeof(void*)*1, x_46);
lean_ctor_set(x_27, 3, x_49);
x_50 = lean_st_ref_set(x_10, x_27, x_29);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4___rarg(x_20, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
x_63 = lean_ctor_get(x_27, 2);
x_64 = lean_ctor_get(x_27, 4);
x_65 = lean_ctor_get(x_27, 5);
x_66 = lean_ctor_get(x_27, 6);
x_67 = lean_ctor_get(x_27, 7);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_68 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_69 = lean_ctor_get(x_28, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_70 = x_28;
} else {
 lean_dec_ref(x_28);
 x_70 = lean_box(0);
}
x_71 = l_Lean_PersistentArray_append___rarg(x_13, x_69);
lean_dec(x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_68);
x_73 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_62);
lean_ctor_set(x_73, 2, x_63);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_64);
lean_ctor_set(x_73, 5, x_65);
lean_ctor_set(x_73, 6, x_66);
lean_ctor_set(x_73, 7, x_67);
x_74 = lean_st_ref_set(x_10, x_73, x_29);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4___rarg(x_20, x_9, x_10, x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; double x_86; double x_87; lean_object* x_88; 
x_85 = lean_box(0);
x_86 = lean_unbox_float(x_21);
lean_dec(x_21);
x_87 = lean_unbox_float(x_22);
lean_dec(x_22);
x_88 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_86, x_87, x_5, x_85, x_9, x_10, x_18);
return x_88;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_io_get_num_heartbeats(x_14);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
lean_inc(x_10);
lean_inc(x_9);
x_304 = lean_apply_3(x_7, x_9, x_10, x_303);
if (lean_obj_tag(x_304) == 0)
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = lean_ctor_get(x_304, 1);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_306);
x_309 = lean_io_get_num_heartbeats(x_307);
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; double x_315; double x_316; lean_object* x_317; lean_object* x_318; 
x_311 = lean_ctor_get(x_309, 0);
x_312 = lean_ctor_get(x_309, 1);
x_313 = 0;
x_314 = lean_unsigned_to_nat(0u);
x_315 = l_Float_ofScientific(x_302, x_313, x_314);
lean_dec(x_302);
x_316 = l_Float_ofScientific(x_311, x_313, x_314);
lean_dec(x_311);
x_317 = lean_box_float(x_315);
x_318 = lean_box_float(x_316);
lean_ctor_set(x_309, 1, x_318);
lean_ctor_set(x_309, 0, x_317);
lean_ctor_set(x_304, 1, x_309);
lean_ctor_set(x_304, 0, x_308);
x_209 = x_304;
x_210 = x_312;
goto block_300;
}
else
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; double x_323; double x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = lean_ctor_get(x_309, 0);
x_320 = lean_ctor_get(x_309, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_309);
x_321 = 0;
x_322 = lean_unsigned_to_nat(0u);
x_323 = l_Float_ofScientific(x_302, x_321, x_322);
lean_dec(x_302);
x_324 = l_Float_ofScientific(x_319, x_321, x_322);
lean_dec(x_319);
x_325 = lean_box_float(x_323);
x_326 = lean_box_float(x_324);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set(x_304, 1, x_327);
lean_ctor_set(x_304, 0, x_308);
x_209 = x_304;
x_210 = x_320;
goto block_300;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; double x_337; double x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_328 = lean_ctor_get(x_304, 0);
x_329 = lean_ctor_get(x_304, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_304);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_328);
x_331 = lean_io_get_num_heartbeats(x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_334 = x_331;
} else {
 lean_dec_ref(x_331);
 x_334 = lean_box(0);
}
x_335 = 0;
x_336 = lean_unsigned_to_nat(0u);
x_337 = l_Float_ofScientific(x_302, x_335, x_336);
lean_dec(x_302);
x_338 = l_Float_ofScientific(x_332, x_335, x_336);
lean_dec(x_332);
x_339 = lean_box_float(x_337);
x_340 = lean_box_float(x_338);
if (lean_is_scalar(x_334)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_334;
}
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_330);
lean_ctor_set(x_342, 1, x_341);
x_209 = x_342;
x_210 = x_333;
goto block_300;
}
}
else
{
uint8_t x_343; 
x_343 = !lean_is_exclusive(x_304);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_344 = lean_ctor_get(x_304, 0);
x_345 = lean_ctor_get(x_304, 1);
x_346 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_346, 0, x_344);
x_347 = lean_io_get_num_heartbeats(x_345);
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; double x_353; double x_354; lean_object* x_355; lean_object* x_356; 
x_349 = lean_ctor_get(x_347, 0);
x_350 = lean_ctor_get(x_347, 1);
x_351 = 0;
x_352 = lean_unsigned_to_nat(0u);
x_353 = l_Float_ofScientific(x_302, x_351, x_352);
lean_dec(x_302);
x_354 = l_Float_ofScientific(x_349, x_351, x_352);
lean_dec(x_349);
x_355 = lean_box_float(x_353);
x_356 = lean_box_float(x_354);
lean_ctor_set(x_347, 1, x_356);
lean_ctor_set(x_347, 0, x_355);
lean_ctor_set_tag(x_304, 0);
lean_ctor_set(x_304, 1, x_347);
lean_ctor_set(x_304, 0, x_346);
x_209 = x_304;
x_210 = x_350;
goto block_300;
}
else
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; double x_361; double x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_357 = lean_ctor_get(x_347, 0);
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_347);
x_359 = 0;
x_360 = lean_unsigned_to_nat(0u);
x_361 = l_Float_ofScientific(x_302, x_359, x_360);
lean_dec(x_302);
x_362 = l_Float_ofScientific(x_357, x_359, x_360);
lean_dec(x_357);
x_363 = lean_box_float(x_361);
x_364 = lean_box_float(x_362);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
lean_ctor_set_tag(x_304, 0);
lean_ctor_set(x_304, 1, x_365);
lean_ctor_set(x_304, 0, x_346);
x_209 = x_304;
x_210 = x_358;
goto block_300;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; double x_375; double x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_366 = lean_ctor_get(x_304, 0);
x_367 = lean_ctor_get(x_304, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_304);
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_366);
x_369 = lean_io_get_num_heartbeats(x_367);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_372 = x_369;
} else {
 lean_dec_ref(x_369);
 x_372 = lean_box(0);
}
x_373 = 0;
x_374 = lean_unsigned_to_nat(0u);
x_375 = l_Float_ofScientific(x_302, x_373, x_374);
lean_dec(x_302);
x_376 = l_Float_ofScientific(x_370, x_373, x_374);
lean_dec(x_370);
x_377 = lean_box_float(x_375);
x_378 = lean_box_float(x_376);
if (lean_is_scalar(x_372)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_372;
}
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_368);
lean_ctor_set(x_380, 1, x_379);
x_209 = x_380;
x_210 = x_371;
goto block_300;
}
}
block_300:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; 
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
x_216 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_215);
if (x_216 == 0)
{
if (x_6 == 0)
{
uint8_t x_282; 
x_282 = 0;
x_217 = x_282;
goto block_281;
}
else
{
lean_object* x_283; double x_284; double x_285; lean_object* x_286; 
x_283 = lean_box(0);
x_284 = lean_unbox_float(x_213);
lean_dec(x_213);
x_285 = lean_unbox_float(x_214);
lean_dec(x_214);
x_286 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__6(x_2, x_3, x_4, x_13, x_212, x_216, x_284, x_285, x_5, x_283, x_9, x_10, x_210);
return x_286;
}
}
else
{
if (x_6 == 0)
{
double x_287; double x_288; double x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; double x_294; uint8_t x_295; 
x_287 = lean_unbox_float(x_214);
x_288 = lean_unbox_float(x_213);
x_289 = lean_float_sub(x_287, x_288);
x_290 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3;
x_291 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_290);
x_292 = 0;
x_293 = lean_unsigned_to_nat(0u);
x_294 = l_Float_ofScientific(x_291, x_292, x_293);
lean_dec(x_291);
x_295 = lean_float_decLt(x_294, x_289);
x_217 = x_295;
goto block_281;
}
else
{
lean_object* x_296; double x_297; double x_298; lean_object* x_299; 
x_296 = lean_box(0);
x_297 = lean_unbox_float(x_213);
lean_dec(x_213);
x_298 = lean_unbox_float(x_214);
lean_dec(x_214);
x_299 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__6(x_2, x_3, x_4, x_13, x_212, x_216, x_297, x_298, x_5, x_296, x_9, x_10, x_210);
return x_299;
}
}
block_281:
{
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_218 = lean_st_ref_take(x_10, x_210);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = !lean_is_exclusive(x_219);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_219, 3);
lean_dec(x_223);
x_224 = !lean_is_exclusive(x_220);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_220, 0);
x_226 = l_Lean_PersistentArray_append___rarg(x_13, x_225);
lean_dec(x_225);
lean_ctor_set(x_220, 0, x_226);
x_227 = lean_st_ref_set(x_10, x_219, x_221);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6___rarg(x_212, x_9, x_10, x_228);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
return x_229;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_229);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
else
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_229);
if (x_234 == 0)
{
return x_229;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_229, 0);
x_236 = lean_ctor_get(x_229, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_229);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint64_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_ctor_get_uint64(x_220, sizeof(void*)*1);
x_239 = lean_ctor_get(x_220, 0);
lean_inc(x_239);
lean_dec(x_220);
x_240 = l_Lean_PersistentArray_append___rarg(x_13, x_239);
lean_dec(x_239);
x_241 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set_uint64(x_241, sizeof(void*)*1, x_238);
lean_ctor_set(x_219, 3, x_241);
x_242 = lean_st_ref_set(x_10, x_219, x_221);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6___rarg(x_212, x_9, x_10, x_243);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_244, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint64_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_253 = lean_ctor_get(x_219, 0);
x_254 = lean_ctor_get(x_219, 1);
x_255 = lean_ctor_get(x_219, 2);
x_256 = lean_ctor_get(x_219, 4);
x_257 = lean_ctor_get(x_219, 5);
x_258 = lean_ctor_get(x_219, 6);
x_259 = lean_ctor_get(x_219, 7);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_219);
x_260 = lean_ctor_get_uint64(x_220, sizeof(void*)*1);
x_261 = lean_ctor_get(x_220, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_262 = x_220;
} else {
 lean_dec_ref(x_220);
 x_262 = lean_box(0);
}
x_263 = l_Lean_PersistentArray_append___rarg(x_13, x_261);
lean_dec(x_261);
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 1, 8);
} else {
 x_264 = x_262;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set_uint64(x_264, sizeof(void*)*1, x_260);
x_265 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_265, 0, x_253);
lean_ctor_set(x_265, 1, x_254);
lean_ctor_set(x_265, 2, x_255);
lean_ctor_set(x_265, 3, x_264);
lean_ctor_set(x_265, 4, x_256);
lean_ctor_set(x_265, 5, x_257);
lean_ctor_set(x_265, 6, x_258);
lean_ctor_set(x_265, 7, x_259);
x_266 = lean_st_ref_set(x_10, x_265, x_221);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6___rarg(x_212, x_9, x_10, x_267);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_268, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_275 = x_268;
} else {
 lean_dec_ref(x_268);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
}
else
{
lean_object* x_277; double x_278; double x_279; lean_object* x_280; 
x_277 = lean_box(0);
x_278 = lean_unbox_float(x_213);
lean_dec(x_213);
x_279 = lean_unbox_float(x_214);
lean_dec(x_214);
x_280 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__6(x_2, x_3, x_4, x_13, x_212, x_216, x_278, x_279, x_5, x_277, x_9, x_10, x_210);
return x_280;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2(x_1, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
x_15 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_apply_3(x_3, x_6, x_7, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_11);
lean_dec(x_11);
x_27 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__7(x_9, x_1, x_4, x_5, x_2, x_26, x_3, x_25, x_6, x_7, x_13);
lean_dec(x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_box(0);
x_30 = lean_unbox(x_11);
lean_dec(x_11);
x_31 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__7(x_9, x_1, x_4, x_5, x_2, x_30, x_3, x_29, x_6, x_7, x_28);
lean_dec(x_9);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_traceBlock___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("blocked", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_traceBlock___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_traceBlock___rarg___lambda__2___closed__1;
x_8 = lean_box(0);
x_9 = l_Lean_profileitM___at_Lean_traceBlock___spec__1___rarg(x_7, x_5, x_6, x_8, x_2, x_3, x_4);
lean_dec(x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_traceBlock___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("block", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_traceBlock___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1;
x_2 = l_Lean_traceBlock___rarg___lambda__3___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_traceBlock___rarg___lambda__2), 4, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_traceBlock___rarg___lambda__3___closed__2;
x_10 = 1;
x_11 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg(x_9, x_7, x_8, x_10, x_1, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_13; lean_object* x_14; 
x_13 = lean_io_get_task_state(x_2, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_6 = x_16;
x_7 = x_15;
goto block_12;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_14);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = 0;
x_6 = x_18;
x_7 = x_17;
goto block_12;
}
block_12:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_traceBlock___rarg___lambda__3(x_1, x_2, x_8, x_3, x_4, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_task_get_own(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_traceBlock___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_traceBlock___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_profileitM___at_Lean_traceBlock___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_MonadExcept_ofExcept___at_Lean_traceBlock___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = lean_unbox_float(x_8);
lean_dec(x_8);
x_17 = lean_unbox_float(x_9);
lean_dec(x_9);
x_18 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__2(x_1, x_14, x_3, x_4, x_5, x_6, x_15, x_16, x_17, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox_float(x_7);
lean_dec(x_7);
x_17 = lean_unbox_float(x_8);
lean_dec(x_8);
x_18 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__3(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = lean_unbox_float(x_8);
lean_dec(x_8);
x_17 = lean_unbox_float(x_9);
lean_dec(x_9);
x_18 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__5(x_1, x_14, x_3, x_4, x_5, x_6, x_15, x_16, x_17, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox_float(x_7);
lean_dec(x_7);
x_17 = lean_unbox_float(x_8);
lean_dec(x_8);
x_18 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__6(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___lambda__7(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_withTraceNode___at_Lean_traceBlock___spec__2___rarg(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_traceBlock___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_traceBlock___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_compileDecls_doCompile___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_7);
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(x_1, x_5, x_2, x_3, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(x_4, x_7, x_8, x_11);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_7 == 0)
{
double x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set_float(x_15, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_15, sizeof(void*)*2 + 8, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 16, x_2);
x_16 = lean_box(0);
x_17 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__1(x_4, x_5, x_10, x_6, x_15, x_16, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_8);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_2);
x_19 = lean_box(0);
x_20 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__1(x_4, x_5, x_10, x_6, x_18, x_19, x_11, x_12, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, double x_7, double x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 5);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_15 = lean_apply_4(x_9, x_5, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_16, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__2;
x_21 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_20, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_5);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__1;
x_16 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_io_mono_nanos_now(x_14);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_10);
lean_inc(x_9);
x_114 = lean_apply_3(x_7, x_9, x_10, x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_119 = lean_io_mono_nanos_now(x_117);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; double x_125; double x_126; double x_127; double x_128; double x_129; lean_object* x_130; lean_object* x_131; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
x_123 = 0;
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Float_ofScientific(x_112, x_123, x_124);
lean_dec(x_112);
x_126 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_127 = lean_float_div(x_125, x_126);
x_128 = l_Float_ofScientific(x_121, x_123, x_124);
lean_dec(x_121);
x_129 = lean_float_div(x_128, x_126);
x_130 = lean_box_float(x_127);
x_131 = lean_box_float(x_129);
lean_ctor_set(x_119, 1, x_131);
lean_ctor_set(x_119, 0, x_130);
lean_ctor_set(x_114, 1, x_119);
lean_ctor_set(x_114, 0, x_118);
x_17 = x_114;
x_18 = x_122;
goto block_110;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; double x_136; double x_137; double x_138; double x_139; double x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_132 = lean_ctor_get(x_119, 0);
x_133 = lean_ctor_get(x_119, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_119);
x_134 = 0;
x_135 = lean_unsigned_to_nat(0u);
x_136 = l_Float_ofScientific(x_112, x_134, x_135);
lean_dec(x_112);
x_137 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_138 = lean_float_div(x_136, x_137);
x_139 = l_Float_ofScientific(x_132, x_134, x_135);
lean_dec(x_132);
x_140 = lean_float_div(x_139, x_137);
x_141 = lean_box_float(x_138);
x_142 = lean_box_float(x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_114, 1, x_143);
lean_ctor_set(x_114, 0, x_118);
x_17 = x_114;
x_18 = x_133;
goto block_110;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; double x_153; double x_154; double x_155; double x_156; double x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_144 = lean_ctor_get(x_114, 0);
x_145 = lean_ctor_get(x_114, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_114);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_144);
x_147 = lean_io_mono_nanos_now(x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = 0;
x_152 = lean_unsigned_to_nat(0u);
x_153 = l_Float_ofScientific(x_112, x_151, x_152);
lean_dec(x_112);
x_154 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_155 = lean_float_div(x_153, x_154);
x_156 = l_Float_ofScientific(x_148, x_151, x_152);
lean_dec(x_148);
x_157 = lean_float_div(x_156, x_154);
x_158 = lean_box_float(x_155);
x_159 = lean_box_float(x_157);
if (lean_is_scalar(x_150)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_150;
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_146);
lean_ctor_set(x_161, 1, x_160);
x_17 = x_161;
x_18 = x_149;
goto block_110;
}
}
else
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_114);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_114, 0);
x_164 = lean_ctor_get(x_114, 1);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_163);
x_166 = lean_io_mono_nanos_now(x_164);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; double x_172; double x_173; double x_174; double x_175; double x_176; lean_object* x_177; lean_object* x_178; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
x_170 = 0;
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_Float_ofScientific(x_112, x_170, x_171);
lean_dec(x_112);
x_173 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_174 = lean_float_div(x_172, x_173);
x_175 = l_Float_ofScientific(x_168, x_170, x_171);
lean_dec(x_168);
x_176 = lean_float_div(x_175, x_173);
x_177 = lean_box_float(x_174);
x_178 = lean_box_float(x_176);
lean_ctor_set(x_166, 1, x_178);
lean_ctor_set(x_166, 0, x_177);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 1, x_166);
lean_ctor_set(x_114, 0, x_165);
x_17 = x_114;
x_18 = x_169;
goto block_110;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; double x_183; double x_184; double x_185; double x_186; double x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_179 = lean_ctor_get(x_166, 0);
x_180 = lean_ctor_get(x_166, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_166);
x_181 = 0;
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Float_ofScientific(x_112, x_181, x_182);
lean_dec(x_112);
x_184 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_185 = lean_float_div(x_183, x_184);
x_186 = l_Float_ofScientific(x_179, x_181, x_182);
lean_dec(x_179);
x_187 = lean_float_div(x_186, x_184);
x_188 = lean_box_float(x_185);
x_189 = lean_box_float(x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 1, x_190);
lean_ctor_set(x_114, 0, x_165);
x_17 = x_114;
x_18 = x_180;
goto block_110;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; double x_200; double x_201; double x_202; double x_203; double x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_191 = lean_ctor_get(x_114, 0);
x_192 = lean_ctor_get(x_114, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_114);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_191);
x_194 = lean_io_mono_nanos_now(x_192);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = 0;
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Float_ofScientific(x_112, x_198, x_199);
lean_dec(x_112);
x_201 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5;
x_202 = lean_float_div(x_200, x_201);
x_203 = l_Float_ofScientific(x_195, x_198, x_199);
lean_dec(x_195);
x_204 = lean_float_div(x_203, x_201);
x_205 = lean_box_float(x_202);
x_206 = lean_box_float(x_204);
if (lean_is_scalar(x_197)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_197;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_193);
lean_ctor_set(x_208, 1, x_207);
x_17 = x_208;
x_18 = x_196;
goto block_110;
}
}
block_110:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
x_24 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_23);
if (x_24 == 0)
{
if (x_6 == 0)
{
uint8_t x_90; 
x_90 = 0;
x_25 = x_90;
goto block_89;
}
else
{
lean_object* x_91; double x_92; double x_93; lean_object* x_94; 
x_91 = lean_box(0);
x_92 = lean_unbox_float(x_21);
lean_dec(x_21);
x_93 = lean_unbox_float(x_22);
lean_dec(x_22);
x_94 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_92, x_93, x_5, x_91, x_9, x_10, x_18);
return x_94;
}
}
else
{
if (x_6 == 0)
{
double x_95; double x_96; double x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; double x_102; double x_103; double x_104; uint8_t x_105; 
x_95 = lean_unbox_float(x_22);
x_96 = lean_unbox_float(x_21);
x_97 = lean_float_sub(x_95, x_96);
x_98 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3;
x_99 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_98);
x_100 = 0;
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Float_ofScientific(x_99, x_100, x_101);
lean_dec(x_99);
x_103 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__4;
x_104 = lean_float_div(x_102, x_103);
x_105 = lean_float_decLt(x_104, x_97);
x_25 = x_105;
goto block_89;
}
else
{
lean_object* x_106; double x_107; double x_108; lean_object* x_109; 
x_106 = lean_box(0);
x_107 = lean_unbox_float(x_21);
lean_dec(x_21);
x_108 = lean_unbox_float(x_22);
lean_dec(x_22);
x_109 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_107, x_108, x_5, x_106, x_9, x_10, x_18);
return x_109;
}
}
block_89:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_st_ref_take(x_10, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 3);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = l_Lean_PersistentArray_append___rarg(x_13, x_33);
lean_dec(x_33);
lean_ctor_set(x_28, 0, x_34);
x_35 = lean_st_ref_set(x_10, x_27, x_29);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(x_20, x_9, x_10, x_36);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
lean_dec(x_28);
x_48 = l_Lean_PersistentArray_append___rarg(x_13, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint64(x_49, sizeof(void*)*1, x_46);
lean_ctor_set(x_27, 3, x_49);
x_50 = lean_st_ref_set(x_10, x_27, x_29);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(x_20, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
x_63 = lean_ctor_get(x_27, 2);
x_64 = lean_ctor_get(x_27, 4);
x_65 = lean_ctor_get(x_27, 5);
x_66 = lean_ctor_get(x_27, 6);
x_67 = lean_ctor_get(x_27, 7);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_68 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_69 = lean_ctor_get(x_28, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_70 = x_28;
} else {
 lean_dec_ref(x_28);
 x_70 = lean_box(0);
}
x_71 = l_Lean_PersistentArray_append___rarg(x_13, x_69);
lean_dec(x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_68);
x_73 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_62);
lean_ctor_set(x_73, 2, x_63);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_64);
lean_ctor_set(x_73, 5, x_65);
lean_ctor_set(x_73, 6, x_66);
lean_ctor_set(x_73, 7, x_67);
x_74 = lean_st_ref_set(x_10, x_73, x_29);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(x_20, x_9, x_10, x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; double x_86; double x_87; lean_object* x_88; 
x_85 = lean_box(0);
x_86 = lean_unbox_float(x_21);
lean_dec(x_21);
x_87 = lean_unbox_float(x_22);
lean_dec(x_22);
x_88 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_86, x_87, x_5, x_85, x_9, x_10, x_18);
return x_88;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_io_get_num_heartbeats(x_14);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
lean_inc(x_10);
lean_inc(x_9);
x_304 = lean_apply_3(x_7, x_9, x_10, x_303);
if (lean_obj_tag(x_304) == 0)
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = lean_ctor_get(x_304, 1);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_306);
x_309 = lean_io_get_num_heartbeats(x_307);
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; double x_315; double x_316; lean_object* x_317; lean_object* x_318; 
x_311 = lean_ctor_get(x_309, 0);
x_312 = lean_ctor_get(x_309, 1);
x_313 = 0;
x_314 = lean_unsigned_to_nat(0u);
x_315 = l_Float_ofScientific(x_302, x_313, x_314);
lean_dec(x_302);
x_316 = l_Float_ofScientific(x_311, x_313, x_314);
lean_dec(x_311);
x_317 = lean_box_float(x_315);
x_318 = lean_box_float(x_316);
lean_ctor_set(x_309, 1, x_318);
lean_ctor_set(x_309, 0, x_317);
lean_ctor_set(x_304, 1, x_309);
lean_ctor_set(x_304, 0, x_308);
x_209 = x_304;
x_210 = x_312;
goto block_300;
}
else
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; double x_323; double x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = lean_ctor_get(x_309, 0);
x_320 = lean_ctor_get(x_309, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_309);
x_321 = 0;
x_322 = lean_unsigned_to_nat(0u);
x_323 = l_Float_ofScientific(x_302, x_321, x_322);
lean_dec(x_302);
x_324 = l_Float_ofScientific(x_319, x_321, x_322);
lean_dec(x_319);
x_325 = lean_box_float(x_323);
x_326 = lean_box_float(x_324);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set(x_304, 1, x_327);
lean_ctor_set(x_304, 0, x_308);
x_209 = x_304;
x_210 = x_320;
goto block_300;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; double x_337; double x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_328 = lean_ctor_get(x_304, 0);
x_329 = lean_ctor_get(x_304, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_304);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_328);
x_331 = lean_io_get_num_heartbeats(x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_334 = x_331;
} else {
 lean_dec_ref(x_331);
 x_334 = lean_box(0);
}
x_335 = 0;
x_336 = lean_unsigned_to_nat(0u);
x_337 = l_Float_ofScientific(x_302, x_335, x_336);
lean_dec(x_302);
x_338 = l_Float_ofScientific(x_332, x_335, x_336);
lean_dec(x_332);
x_339 = lean_box_float(x_337);
x_340 = lean_box_float(x_338);
if (lean_is_scalar(x_334)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_334;
}
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_330);
lean_ctor_set(x_342, 1, x_341);
x_209 = x_342;
x_210 = x_333;
goto block_300;
}
}
else
{
uint8_t x_343; 
x_343 = !lean_is_exclusive(x_304);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_344 = lean_ctor_get(x_304, 0);
x_345 = lean_ctor_get(x_304, 1);
x_346 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_346, 0, x_344);
x_347 = lean_io_get_num_heartbeats(x_345);
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; double x_353; double x_354; lean_object* x_355; lean_object* x_356; 
x_349 = lean_ctor_get(x_347, 0);
x_350 = lean_ctor_get(x_347, 1);
x_351 = 0;
x_352 = lean_unsigned_to_nat(0u);
x_353 = l_Float_ofScientific(x_302, x_351, x_352);
lean_dec(x_302);
x_354 = l_Float_ofScientific(x_349, x_351, x_352);
lean_dec(x_349);
x_355 = lean_box_float(x_353);
x_356 = lean_box_float(x_354);
lean_ctor_set(x_347, 1, x_356);
lean_ctor_set(x_347, 0, x_355);
lean_ctor_set_tag(x_304, 0);
lean_ctor_set(x_304, 1, x_347);
lean_ctor_set(x_304, 0, x_346);
x_209 = x_304;
x_210 = x_350;
goto block_300;
}
else
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; double x_361; double x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_357 = lean_ctor_get(x_347, 0);
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_347);
x_359 = 0;
x_360 = lean_unsigned_to_nat(0u);
x_361 = l_Float_ofScientific(x_302, x_359, x_360);
lean_dec(x_302);
x_362 = l_Float_ofScientific(x_357, x_359, x_360);
lean_dec(x_357);
x_363 = lean_box_float(x_361);
x_364 = lean_box_float(x_362);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
lean_ctor_set_tag(x_304, 0);
lean_ctor_set(x_304, 1, x_365);
lean_ctor_set(x_304, 0, x_346);
x_209 = x_304;
x_210 = x_358;
goto block_300;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; double x_375; double x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_366 = lean_ctor_get(x_304, 0);
x_367 = lean_ctor_get(x_304, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_304);
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_366);
x_369 = lean_io_get_num_heartbeats(x_367);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_372 = x_369;
} else {
 lean_dec_ref(x_369);
 x_372 = lean_box(0);
}
x_373 = 0;
x_374 = lean_unsigned_to_nat(0u);
x_375 = l_Float_ofScientific(x_302, x_373, x_374);
lean_dec(x_302);
x_376 = l_Float_ofScientific(x_370, x_373, x_374);
lean_dec(x_370);
x_377 = lean_box_float(x_375);
x_378 = lean_box_float(x_376);
if (lean_is_scalar(x_372)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_372;
}
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_368);
lean_ctor_set(x_380, 1, x_379);
x_209 = x_380;
x_210 = x_371;
goto block_300;
}
}
block_300:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; 
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
x_216 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_215);
if (x_216 == 0)
{
if (x_6 == 0)
{
uint8_t x_282; 
x_282 = 0;
x_217 = x_282;
goto block_281;
}
else
{
lean_object* x_283; double x_284; double x_285; lean_object* x_286; 
x_283 = lean_box(0);
x_284 = lean_unbox_float(x_213);
lean_dec(x_213);
x_285 = lean_unbox_float(x_214);
lean_dec(x_214);
x_286 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3(x_2, x_3, x_4, x_13, x_212, x_216, x_284, x_285, x_5, x_283, x_9, x_10, x_210);
return x_286;
}
}
else
{
if (x_6 == 0)
{
double x_287; double x_288; double x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; double x_294; uint8_t x_295; 
x_287 = lean_unbox_float(x_214);
x_288 = lean_unbox_float(x_213);
x_289 = lean_float_sub(x_287, x_288);
x_290 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3;
x_291 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_290);
x_292 = 0;
x_293 = lean_unsigned_to_nat(0u);
x_294 = l_Float_ofScientific(x_291, x_292, x_293);
lean_dec(x_291);
x_295 = lean_float_decLt(x_294, x_289);
x_217 = x_295;
goto block_281;
}
else
{
lean_object* x_296; double x_297; double x_298; lean_object* x_299; 
x_296 = lean_box(0);
x_297 = lean_unbox_float(x_213);
lean_dec(x_213);
x_298 = lean_unbox_float(x_214);
lean_dec(x_214);
x_299 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3(x_2, x_3, x_4, x_13, x_212, x_216, x_297, x_298, x_5, x_296, x_9, x_10, x_210);
return x_299;
}
}
block_281:
{
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_218 = lean_st_ref_take(x_10, x_210);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = !lean_is_exclusive(x_219);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_219, 3);
lean_dec(x_223);
x_224 = !lean_is_exclusive(x_220);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_220, 0);
x_226 = l_Lean_PersistentArray_append___rarg(x_13, x_225);
lean_dec(x_225);
lean_ctor_set(x_220, 0, x_226);
x_227 = lean_st_ref_set(x_10, x_219, x_221);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(x_212, x_9, x_10, x_228);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
return x_229;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_229);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
else
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_229);
if (x_234 == 0)
{
return x_229;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_229, 0);
x_236 = lean_ctor_get(x_229, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_229);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint64_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_ctor_get_uint64(x_220, sizeof(void*)*1);
x_239 = lean_ctor_get(x_220, 0);
lean_inc(x_239);
lean_dec(x_220);
x_240 = l_Lean_PersistentArray_append___rarg(x_13, x_239);
lean_dec(x_239);
x_241 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set_uint64(x_241, sizeof(void*)*1, x_238);
lean_ctor_set(x_219, 3, x_241);
x_242 = lean_st_ref_set(x_10, x_219, x_221);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(x_212, x_9, x_10, x_243);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_244, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint64_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_253 = lean_ctor_get(x_219, 0);
x_254 = lean_ctor_get(x_219, 1);
x_255 = lean_ctor_get(x_219, 2);
x_256 = lean_ctor_get(x_219, 4);
x_257 = lean_ctor_get(x_219, 5);
x_258 = lean_ctor_get(x_219, 6);
x_259 = lean_ctor_get(x_219, 7);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_219);
x_260 = lean_ctor_get_uint64(x_220, sizeof(void*)*1);
x_261 = lean_ctor_get(x_220, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_262 = x_220;
} else {
 lean_dec_ref(x_220);
 x_262 = lean_box(0);
}
x_263 = l_Lean_PersistentArray_append___rarg(x_13, x_261);
lean_dec(x_261);
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 1, 8);
} else {
 x_264 = x_262;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set_uint64(x_264, sizeof(void*)*1, x_260);
x_265 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_265, 0, x_253);
lean_ctor_set(x_265, 1, x_254);
lean_ctor_set(x_265, 2, x_255);
lean_ctor_set(x_265, 3, x_264);
lean_ctor_set(x_265, 4, x_256);
lean_ctor_set(x_265, 5, x_257);
lean_ctor_set(x_265, 6, x_258);
lean_ctor_set(x_265, 7, x_259);
x_266 = lean_st_ref_set(x_10, x_265, x_221);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(x_212, x_9, x_10, x_267);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_268, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_275 = x_268;
} else {
 lean_dec_ref(x_268);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
}
else
{
lean_object* x_277; double x_278; double x_279; lean_object* x_280; 
x_277 = lean_box(0);
x_278 = lean_unbox_float(x_213);
lean_dec(x_213);
x_279 = lean_unbox_float(x_214);
lean_dec(x_214);
x_280 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3(x_2, x_3, x_4, x_13, x_212, x_216, x_278, x_279, x_5, x_277, x_9, x_10, x_210);
return x_280;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2(x_1, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2;
x_15 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_apply_3(x_3, x_6, x_7, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_11);
lean_dec(x_11);
x_27 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__4(x_9, x_1, x_4, x_5, x_2, x_26, x_3, x_25, x_6, x_7, x_13);
lean_dec(x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_box(0);
x_30 = lean_unbox(x_11);
lean_dec(x_11);
x_31 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__4(x_9, x_1, x_4, x_5, x_2, x_30, x_3, x_29, x_6, x_7, x_28);
lean_dec(x_9);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_compileDecls_doCompile___spec__5___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_compileDecls_doCompile___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_throwInterruptException___at_Lean_compileDecls_doCompile___spec__5___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l_Lean_Kernel_Exception_toMessageData(x_1, x_6);
x_8 = l_Lean_throwError___at_Lean_Core_instantiateValueLevelParams___spec__1(x_7, x_3, x_4, x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 16)
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = l_Lean_throwInterruptException___at_Lean_compileDecls_doCompile___spec__5___rarg(x_4);
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
x_11 = l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4___lambda__1(x_1, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_10 = x_3;
} else {
 lean_dec_ref(x_3);
 x_10 = lean_box(0);
}
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_1);
x_34 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_34, 0, x_1);
x_35 = lean_find_expr(x_34, x_33);
lean_dec(x_33);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
x_11 = x_6;
goto block_31;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofName(x_37);
x_39 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_42, x_4, x_5, x_6);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_dec(x_36);
x_11 = x_6;
goto block_31;
}
}
block_31:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = lean_find_expr(x_13, x_12);
lean_dec(x_12);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_box(0);
x_2 = x_15;
x_3 = x_9;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_MessageData_ofName(x_18);
x_20 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
if (lean_is_scalar(x_10)) {
 x_21 = lean_alloc_ctor(7, 2, 0);
} else {
 x_21 = x_10;
 lean_ctor_set_tag(x_21, 7);
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_23, x_4, x_5, x_11);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_17);
lean_dec(x_10);
x_29 = lean_box(0);
x_2 = x_29;
x_3 = x_9;
x_6 = x_11;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_find_expr(x_12, x_11);
lean_dec(x_11);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_free_object(x_3);
x_14 = lean_box(0);
x_2 = x_14;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_MessageData_ofName(x_17);
x_19 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_19);
x_20 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_21, x_4, x_5, x_6);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_16);
lean_free_object(x_3);
x_27 = lean_box(0);
x_2 = x_27;
x_3 = x_10;
goto _start;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_1);
x_32 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = lean_find_expr(x_32, x_31);
lean_dec(x_31);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_2 = x_34;
x_3 = x_30;
goto _start;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_30);
lean_dec(x_1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofName(x_37);
x_39 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_42, x_4, x_5, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_36);
x_48 = lean_box(0);
x_2 = x_48;
x_3 = x_30;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_1);
x_22 = lean_find_expr(x_21, x_20);
lean_dec(x_20);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_3);
x_23 = lean_ctor_get(x_9, 2);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_box(0);
lean_inc(x_1);
x_25 = l_List_foldlM___at_Lean_compileDecls_doCompile___spec__10(x_1, x_24, x_23, x_4, x_5, x_6);
x_11 = x_25;
goto block_19;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_9);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_MessageData_ofName(x_27);
x_29 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_28);
lean_ctor_set(x_3, 0, x_29);
x_30 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_31, x_4, x_5, x_6);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
x_11 = x_32;
goto block_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_11 = x_36;
goto block_19;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
lean_free_object(x_3);
x_37 = lean_ctor_get(x_9, 2);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_box(0);
lean_inc(x_1);
x_39 = l_List_foldlM___at_Lean_compileDecls_doCompile___spec__10(x_1, x_38, x_37, x_4, x_5, x_6);
x_11 = x_39;
goto block_19;
}
}
block_19:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_2 = x_12;
x_3 = x_10;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_inc(x_1);
x_52 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_52, 0, x_1);
x_53 = lean_find_expr(x_52, x_51);
lean_dec(x_51);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 2);
lean_inc(x_54);
lean_dec(x_40);
x_55 = lean_box(0);
lean_inc(x_1);
x_56 = l_List_foldlM___at_Lean_compileDecls_doCompile___spec__10(x_1, x_55, x_54, x_4, x_5, x_6);
x_42 = x_56;
goto block_50;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
if (lean_obj_tag(x_57) == 4)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_40);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_MessageData_ofName(x_58);
x_60 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_63, x_4, x_5, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
x_42 = x_68;
goto block_50;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_57);
x_69 = lean_ctor_get(x_40, 2);
lean_inc(x_69);
lean_dec(x_40);
x_70 = lean_box(0);
lean_inc(x_1);
x_71 = l_List_foldlM___at_Lean_compileDecls_doCompile___spec__10(x_1, x_70, x_69, x_4, x_5, x_6);
x_42 = x_71;
goto block_50;
}
}
block_50:
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_2 = x_43;
x_3 = x_41;
x_6 = x_44;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_41);
lean_dec(x_1);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_compileDecls_doCompile___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_find_expr(x_10, x_9);
lean_dec(x_9);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_MessageData_ofName(x_15);
x_17 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_20, x_4, x_5, x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_44; lean_object* x_45; 
lean_dec(x_3);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_44 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_44, 0, x_1);
x_45 = lean_find_expr(x_44, x_27);
lean_dec(x_27);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
x_28 = x_6;
goto block_43;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 4)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_26);
lean_dec(x_1);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_MessageData_ofName(x_47);
x_49 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_52, x_4, x_5, x_6);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_dec(x_46);
x_28 = x_6;
goto block_43;
}
}
block_43:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_29, 0, x_1);
x_30 = lean_find_expr(x_29, x_26);
lean_dec(x_26);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_MessageData_ofName(x_34);
x_36 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_39, x_4, x_5, x_28);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_28);
return x_42;
}
}
}
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_78; lean_object* x_79; 
lean_dec(x_3);
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
lean_dec(x_2);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 2);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_1);
x_78 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_78, 0, x_1);
x_79 = lean_find_expr(x_78, x_61);
lean_dec(x_61);
lean_dec(x_78);
if (lean_obj_tag(x_79) == 0)
{
x_62 = x_6;
goto block_77;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 4)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_60);
lean_dec(x_1);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_MessageData_ofName(x_81);
x_83 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_86, x_4, x_5, x_6);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_dec(x_80);
x_62 = x_6;
goto block_77;
}
}
block_77:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_63, 0, x_1);
x_64 = lean_find_expr(x_63, x_60);
lean_dec(x_60);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
if (lean_obj_tag(x_67) == 4)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_MessageData_ofName(x_68);
x_70 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_73, x_4, x_5, x_62);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_62);
return x_76;
}
}
}
}
case 3:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_112; lean_object* x_113; 
lean_dec(x_3);
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
lean_dec(x_2);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 2);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_1);
x_112 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_112, 0, x_1);
x_113 = lean_find_expr(x_112, x_95);
lean_dec(x_95);
lean_dec(x_112);
if (lean_obj_tag(x_113) == 0)
{
x_96 = x_6;
goto block_111;
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 4)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_94);
lean_dec(x_1);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_MessageData_ofName(x_115);
x_117 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_120, x_4, x_5, x_6);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_121);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_dec(x_114);
x_96 = x_6;
goto block_111;
}
}
block_111:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_97, 0, x_1);
x_98 = lean_find_expr(x_97, x_94);
lean_dec(x_94);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
lean_dec(x_98);
if (lean_obj_tag(x_101) == 4)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_MessageData_ofName(x_102);
x_104 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_107, x_4, x_5, x_96);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_101);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_96);
return x_110;
}
}
}
}
case 4:
{
lean_object* x_126; 
lean_dec(x_1);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_3);
lean_ctor_set(x_126, 1, x_6);
return x_126;
}
case 5:
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_2, 0);
lean_inc(x_127);
lean_dec(x_2);
x_128 = l_List_foldlM___at_Lean_compileDecls_doCompile___spec__9(x_1, x_3, x_127, x_4, x_5, x_6);
return x_128;
}
default: 
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_2, 2);
lean_inc(x_129);
lean_dec(x_2);
x_130 = l_List_foldlM___at_Lean_compileDecls_doCompile___spec__11(x_1, x_3, x_129, x_4, x_5, x_6);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at_Lean_compileDecls_doCompile___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = l_Lean_Declaration_foldExprM___at_Lean_compileDecls_doCompile___spec__8(x_8, x_1, x_9, x_2, x_3, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 4);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = l_Lean_Core_instInhabitedCache___closed__3;
lean_ctor_set(x_6, 4, x_11);
lean_ctor_set(x_6, 0, x_1);
x_12 = lean_st_ref_set(x_3, x_6, x_7);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 5);
x_23 = lean_ctor_get(x_6, 6);
x_24 = lean_ctor_get(x_6, 7);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_25 = l_Lean_Core_instInhabitedCache___closed__3;
x_26 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_22);
lean_ctor_set(x_26, 6, x_23);
lean_ctor_set(x_26, 7, x_24);
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
static lean_object* _init_l_Lean_compileDecls_doCompile___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiling old: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_compileDecls_doCompile___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_compileDecls_doCompile___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at_Lean_compileDecls_doCompile___spec__1(x_1, x_6);
x_8 = l_Lean_MessageData_ofList(x_7);
x_9 = l_Lean_compileDecls_doCompile___lambda__1___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = l_Lean_throwError___at_Lean_Core_instantiateValueLevelParams___spec__1(x_7, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_compileDecls_doCompile___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_compiler_enableNew;
return x_1;
}
}
static lean_object* _init_l_Lean_compileDecls_doCompile___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = l_Lean_compileDecls_doCompile___lambda__4___closed__1;
x_10 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lambda__1___boxed), 5, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lambda__2___boxed), 5, 2);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_1);
x_13 = l_Lean_compileDecls_doCompile___lambda__4___closed__2;
x_14 = 1;
x_15 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2(x_13, x_11, x_12, x_14, x_15, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 12)
{
if (x_2 == 0)
{
uint8_t x_19; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = l_Lean_compileDecls_doCompile___lambda__3(x_26, x_27, x_5, x_6, x_25);
lean_dec(x_6);
lean_dec(x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec(x_3);
x_32 = l___private_Lean_CoreM_0__Lean_checkUnsupported___at_Lean_compileDecls_doCompile___spec__6(x_31, x_5, x_6, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_compileDecls_doCompile___lambda__3(x_30, x_33, x_5, x_6, x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
else
{
lean_dec(x_3);
if (x_2 == 0)
{
uint8_t x_40; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_16, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_16, 0, x_42);
return x_16;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_dec(x_16);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_dec(x_16);
x_47 = l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4(x_18, x_5, x_6, x_46);
lean_dec(x_6);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_ctor_get(x_17, 0);
lean_inc(x_49);
lean_dec(x_17);
x_50 = l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(x_49, x_5, x_6, x_48);
lean_dec(x_6);
lean_dec(x_5);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_16);
if (x_51 == 0)
{
return x_16;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_16, 0);
x_53 = lean_ctor_get(x_16, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_16);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_8);
lean_dec(x_3);
x_55 = lean_lcnf_compile_decls(x_1, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
if (x_2 == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set_tag(x_55, 0);
lean_ctor_set(x_55, 0, x_62);
return x_55;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_55);
if (x_66 == 0)
{
return x_55;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_55, 0);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_55);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
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
x_13 = lean_alloc_closure((void*)(l_Lean_SMap_contains___at_Lean_Environment_addExtraName___spec__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
lean_inc(x_1);
x_14 = l_List_all___rarg(x_1, x_13);
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
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_7);
x_16 = lean_box(0);
x_17 = l_Lean_compileDecls_doCompile___lambda__4(x_1, x_3, x_2, x_16, x_4, x_5, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Environment_constants(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_SMap_contains___at_Lean_Environment_addExtraName___spec__1___boxed), 2, 1);
lean_closure_set(x_22, 0, x_21);
lean_inc(x_1);
x_23 = l_List_all___rarg(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_compileDecls_doCompile___lambda__4(x_1, x_3, x_2, x_26, x_4, x_5, x_19);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_MonadExcept_ofExcept___at_Lean_compileDecls_doCompile___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = lean_unbox_float(x_8);
lean_dec(x_8);
x_17 = lean_unbox_float(x_9);
lean_dec(x_9);
x_18 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__2(x_1, x_14, x_3, x_4, x_5, x_6, x_15, x_16, x_17, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox_float(x_7);
lean_dec(x_7);
x_17 = lean_unbox_float(x_8);
lean_dec(x_8);
x_18 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__3(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___lambda__4(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_withTraceNode___at_Lean_compileDecls_doCompile___spec__2(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_compileDecls_doCompile___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwInterruptException___at_Lean_compileDecls_doCompile___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwKernelException___at_Lean_compileDecls_doCompile___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_compileDecls_doCompile___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at_Lean_compileDecls_doCompile___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at_Lean_compileDecls_doCompile___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_compileDecls_doCompile___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at_Lean_compileDecls_doCompile___spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_compileDecls_doCompile___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Declaration_foldExprM___at_Lean_compileDecls_doCompile___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at_Lean_compileDecls_doCompile___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_checkUnsupported___at_Lean_compileDecls_doCompile___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_compileDecls_doCompile___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_compileDecls_doCompile___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_compileDecls_doCompile___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_compileDecls_doCompile___lambda__4(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_compileDecls___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(x_9, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_7);
x_12 = l_Lean_compileDecls_doCompile(x_2, x_3, x_4, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_7, x_14);
lean_dec(x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Environment_PromiseCheckedResult_commitChecked(x_1, x_18, x_17);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_st_ref_get(x_7, x_25);
lean_dec(x_7);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Environment_PromiseCheckedResult_commitChecked(x_1, x_29, x_28);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_24);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_compileDecls___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compileDecls", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_compileDecls___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_2 = l_Lean_compileDecls___lambda__2___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_compileDecls___lambda__2___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_compileDecls___lambda__2___closed__2;
x_2 = 1;
x_3 = l_Lean_useDiagnosticMsg___lambda__2___closed__2;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_11);
x_12 = l_Lean_Environment_promiseChecked(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(x_15, x_5, x_6, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_IO_CancelToken_new(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(x_3);
x_22 = lean_alloc_closure((void*)(l_Lean_compileDecls___lambda__1___boxed), 8, 4);
lean_closure_set(x_22, 0, x_13);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_24 = l_Lean_compileDecls___lambda__2___closed__3;
lean_inc(x_5);
lean_inc(x_23);
x_25 = l_Lean_Core_wrapAsyncAsSnapshot___rarg(x_22, x_23, x_24, x_5, x_6, x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_11, 2);
lean_inc(x_28);
lean_dec(x_11);
x_29 = l_Task_Priority_default;
x_30 = 0;
x_31 = lean_io_map_task(x_26, x_28, x_29, x_30, x_27);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_5, 5);
lean_inc(x_35);
x_36 = l_Lean_Syntax_getTailPos_x3f(x_35, x_30);
lean_dec(x_35);
x_37 = lean_box(0);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_31);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_23);
lean_ctor_set(x_38, 3, x_33);
x_39 = l_Lean_Core_logSnapshotTask(x_38, x_5, x_6, x_34);
lean_dec(x_5);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_ctor_set(x_31, 1, x_41);
lean_ctor_set(x_31, 0, x_41);
lean_ctor_set(x_36, 0, x_31);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_23);
lean_ctor_set(x_42, 3, x_33);
x_43 = l_Lean_Core_logSnapshotTask(x_42, x_5, x_6, x_34);
lean_dec(x_5);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_dec(x_36);
lean_inc(x_44);
lean_ctor_set(x_31, 1, x_44);
lean_ctor_set(x_31, 0, x_44);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_31);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_23);
lean_ctor_set(x_46, 3, x_33);
x_47 = l_Lean_Core_logSnapshotTask(x_46, x_5, x_6, x_34);
lean_dec(x_5);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_ctor_get(x_5, 5);
lean_inc(x_50);
x_51 = l_Lean_Syntax_getTailPos_x3f(x_50, x_30);
lean_dec(x_50);
x_52 = lean_box(0);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_23);
lean_ctor_set(x_53, 3, x_48);
x_54 = l_Lean_Core_logSnapshotTask(x_53, x_5, x_6, x_49);
lean_dec(x_5);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_56 = x_51;
} else {
 lean_dec_ref(x_51);
 x_56 = lean_box(0);
}
lean_inc(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_55);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_23);
lean_ctor_set(x_59, 3, x_48);
x_60 = l_Lean_Core_logSnapshotTask(x_59, x_5, x_6, x_49);
lean_dec(x_5);
return x_60;
}
}
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
x_1 = lean_mk_string_unchecked("compiler env", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_compileDecls___closed__1;
x_13 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_12);
lean_dec(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_14 = lean_st_ref_get(x_5, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_compileDecls___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_traceBlock___rarg(x_19, x_18, x_4, x_5, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_compileDecls_doCompile(x_1, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = l_Lean_Environment_isRealizing(x_11);
lean_dec(x_11);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Lean_compileDecls___lambda__2(x_1, x_2, x_3, x_38, x_4, x_5, x_10);
lean_dec(x_5);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_st_ref_get(x_5, x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_compileDecls___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_46 = l_Lean_traceBlock___rarg(x_45, x_44, x_4, x_5, x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_compileDecls_doCompile(x_1, x_2, x_3, x_4, x_5, x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_46);
if (x_59 == 0)
{
return x_46;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_46, 0);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_46);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_compileDecls___lambda__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_compileDecls___lambda__2(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
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
x_2 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_3 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*13);
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
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
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_7, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_dec(x_12);
x_13 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1;
x_14 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_13);
lean_ctor_set(x_7, 4, x_14);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*13, x_2);
x_15 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_16 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_3, x_15);
x_17 = lean_st_ref_get(x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Kernel_isDiagnosticsEnabled(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
if (x_16 == 0)
{
uint8_t x_50; 
x_50 = 1;
x_22 = x_50;
goto block_49;
}
else
{
uint8_t x_51; 
x_51 = 0;
x_22 = x_51;
goto block_49;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_52; 
x_52 = 0;
x_22 = x_52;
goto block_49;
}
else
{
uint8_t x_53; 
x_53 = 1;
x_22 = x_53;
goto block_49;
}
}
block_49:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_st_ref_take(x_8, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 4);
lean_dec(x_28);
x_29 = l_Lean_Kernel_enableDiag(x_27, x_16);
lean_ctor_set(x_24, 4, x_5);
lean_ctor_set(x_24, 0, x_29);
x_30 = lean_st_ref_set(x_8, x_24, x_25);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_3, x_16, x_4, x_32, x_7, x_8, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
x_36 = lean_ctor_get(x_24, 2);
x_37 = lean_ctor_get(x_24, 3);
x_38 = lean_ctor_get(x_24, 5);
x_39 = lean_ctor_get(x_24, 6);
x_40 = lean_ctor_get(x_24, 7);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_41 = l_Lean_Kernel_enableDiag(x_34, x_16);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 4, x_5);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_42, 6, x_39);
lean_ctor_set(x_42, 7, x_40);
x_43 = lean_st_ref_set(x_8, x_42, x_25);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_3, x_16, x_4, x_45, x_7, x_8, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_5);
x_47 = lean_box(0);
x_48 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_3, x_16, x_4, x_47, x_7, x_8, x_19);
return x_48;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
x_56 = lean_ctor_get(x_7, 3);
x_57 = lean_ctor_get(x_7, 5);
x_58 = lean_ctor_get(x_7, 6);
x_59 = lean_ctor_get(x_7, 7);
x_60 = lean_ctor_get(x_7, 8);
x_61 = lean_ctor_get(x_7, 9);
x_62 = lean_ctor_get(x_7, 10);
x_63 = lean_ctor_get(x_7, 11);
x_64 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_65 = lean_ctor_get(x_7, 12);
lean_inc(x_65);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_66 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1;
x_67 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_66);
x_68 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_55);
lean_ctor_set(x_68, 2, x_1);
lean_ctor_set(x_68, 3, x_56);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_57);
lean_ctor_set(x_68, 6, x_58);
lean_ctor_set(x_68, 7, x_59);
lean_ctor_set(x_68, 8, x_60);
lean_ctor_set(x_68, 9, x_61);
lean_ctor_set(x_68, 10, x_62);
lean_ctor_set(x_68, 11, x_63);
lean_ctor_set(x_68, 12, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_68, sizeof(void*)*13 + 1, x_64);
x_69 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_70 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_3, x_69);
x_71 = lean_st_ref_get(x_8, x_9);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Kernel_isDiagnosticsEnabled(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
if (x_70 == 0)
{
uint8_t x_97; 
x_97 = 1;
x_76 = x_97;
goto block_96;
}
else
{
uint8_t x_98; 
x_98 = 0;
x_76 = x_98;
goto block_96;
}
}
else
{
if (x_70 == 0)
{
uint8_t x_99; 
x_99 = 0;
x_76 = x_99;
goto block_96;
}
else
{
uint8_t x_100; 
x_100 = 1;
x_76 = x_100;
goto block_96;
}
}
block_96:
{
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_77 = lean_st_ref_take(x_8, x_73);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 7);
lean_inc(x_86);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 lean_ctor_release(x_78, 6);
 lean_ctor_release(x_78, 7);
 x_87 = x_78;
} else {
 lean_dec_ref(x_78);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Kernel_enableDiag(x_80, x_70);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 8, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_81);
lean_ctor_set(x_89, 2, x_82);
lean_ctor_set(x_89, 3, x_83);
lean_ctor_set(x_89, 4, x_5);
lean_ctor_set(x_89, 5, x_84);
lean_ctor_set(x_89, 6, x_85);
lean_ctor_set(x_89, 7, x_86);
x_90 = lean_st_ref_set(x_8, x_89, x_79);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
x_93 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_3, x_70, x_4, x_92, x_68, x_8, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
x_94 = lean_box(0);
x_95 = l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1(x_3, x_70, x_4, x_94, x_68, x_8, x_73);
return x_95;
}
}
}
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3;
x_2 = l___auto____x40_Lean_CoreM___hyg_3975____closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_ImportM_runCoreM___rarg___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ImportM_runCoreM___rarg___closed__5;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___rarg___closed__7() {
_start:
{
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1___closed__4;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<ImportM>", 9, 9);
return x_1;
}
}
static uint8_t _init_l_Lean_ImportM_runCoreM___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_useDiagnosticMsg___lambda__2___closed__1;
x_3 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_17; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; 
x_48 = lean_box(0);
x_49 = lean_box(0);
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_dec(x_2);
x_52 = l_Lean_ImportM_runCoreM___rarg___closed__3;
x_53 = l_Lean_ImportM_runCoreM___rarg___closed__6;
x_54 = l_Lean_ImportM_runCoreM___rarg___closed__7;
x_55 = l_Lean_Core_instInhabitedCache___closed__3;
x_56 = l_Lean_Core_resetMessageLog___closed__1;
x_57 = l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2___closed__1;
x_58 = l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1;
x_59 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_54);
lean_ctor_set(x_59, 4, x_55);
lean_ctor_set(x_59, 5, x_56);
lean_ctor_set(x_59, 6, x_57);
lean_ctor_set(x_59, 7, x_58);
x_60 = lean_io_get_num_heartbeats(x_3);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_st_mk_ref(x_59, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_78 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1;
x_79 = lean_st_ref_get(x_78, x_65);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_ImportM_runCoreM___rarg___closed__8;
x_83 = l_Lean_ImportM_runCoreM___rarg___closed__1;
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_unsigned_to_nat(1000u);
x_86 = lean_box(0);
x_87 = lean_box(0);
x_88 = l_Lean_ImportM_runCoreM___rarg___closed__2;
x_89 = l_Lean_firstFrontendMacroScope;
x_90 = 0;
x_91 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_91, 0, x_82);
lean_ctor_set(x_91, 1, x_83);
lean_ctor_set(x_91, 2, x_48);
lean_ctor_set(x_91, 3, x_84);
lean_ctor_set(x_91, 4, x_85);
lean_ctor_set(x_91, 5, x_86);
lean_ctor_set(x_91, 6, x_87);
lean_ctor_set(x_91, 7, x_48);
lean_ctor_set(x_91, 8, x_61);
lean_ctor_set(x_91, 9, x_88);
lean_ctor_set(x_91, 10, x_89);
lean_ctor_set(x_91, 11, x_49);
lean_ctor_set(x_91, 12, x_80);
lean_ctor_set_uint8(x_91, sizeof(void*)*13, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*13 + 1, x_90);
x_92 = lean_st_ref_get(x_64, x_81);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Kernel_isDiagnosticsEnabled(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_ImportM_runCoreM___rarg___closed__9;
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = 1;
x_97 = x_147;
goto block_145;
}
else
{
x_97 = x_90;
goto block_145;
}
}
else
{
uint8_t x_148; 
x_148 = l_Lean_ImportM_runCoreM___rarg___closed__9;
if (x_148 == 0)
{
x_97 = x_90;
goto block_145;
}
else
{
uint8_t x_149; 
x_149 = 1;
x_97 = x_149;
goto block_145;
}
}
block_16:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
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
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
block_47:
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
x_4 = x_17;
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_4 = x_21;
goto block_16;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MessageData_toString(x_24, x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_28);
x_4 = x_25;
goto block_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_4 = x_32;
goto block_16;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_17, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
x_36 = l___private_Init_Data_Repr_0__Nat_reprFast(x_35);
x_37 = l_Lean_Core_CoreM_toIO___rarg___closed__1;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_17, 0, x_39);
x_4 = x_17;
goto block_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l___private_Init_Data_Repr_0__Nat_reprFast(x_41);
x_43 = l_Lean_Core_CoreM_toIO___rarg___closed__1;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
x_4 = x_46;
goto block_16;
}
}
}
}
block_77:
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_st_ref_get(x_64, x_68);
lean_dec(x_64);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
if (lean_is_scalar(x_66)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_66;
}
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_69, 0, x_72);
x_17 = x_69;
goto block_47;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
if (lean_is_scalar(x_66)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_66;
}
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_17 = x_76;
goto block_47;
}
}
block_145:
{
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_st_ref_take(x_64, x_94);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_99, 0);
x_103 = lean_ctor_get(x_99, 4);
lean_dec(x_103);
x_104 = l_Lean_ImportM_runCoreM___rarg___closed__9;
x_105 = l_Lean_Kernel_enableDiag(x_102, x_104);
lean_ctor_set(x_99, 4, x_55);
lean_ctor_set(x_99, 0, x_105);
x_106 = lean_st_ref_set(x_64, x_99, x_100);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_box(0);
lean_inc(x_64);
x_109 = l_Lean_ImportM_runCoreM___rarg___lambda__1(x_48, x_104, x_51, x_1, x_55, x_108, x_91, x_64, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_67 = x_110;
x_68 = x_111;
goto block_77;
}
else
{
uint8_t x_112; 
lean_dec(x_66);
lean_dec(x_64);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
x_17 = x_109;
goto block_47;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_17 = x_115;
goto block_47;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_116 = lean_ctor_get(x_99, 0);
x_117 = lean_ctor_get(x_99, 1);
x_118 = lean_ctor_get(x_99, 2);
x_119 = lean_ctor_get(x_99, 3);
x_120 = lean_ctor_get(x_99, 5);
x_121 = lean_ctor_get(x_99, 6);
x_122 = lean_ctor_get(x_99, 7);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_99);
x_123 = l_Lean_ImportM_runCoreM___rarg___closed__9;
x_124 = l_Lean_Kernel_enableDiag(x_116, x_123);
x_125 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set(x_125, 2, x_118);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set(x_125, 4, x_55);
lean_ctor_set(x_125, 5, x_120);
lean_ctor_set(x_125, 6, x_121);
lean_ctor_set(x_125, 7, x_122);
x_126 = lean_st_ref_set(x_64, x_125, x_100);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_box(0);
lean_inc(x_64);
x_129 = l_Lean_ImportM_runCoreM___rarg___lambda__1(x_48, x_123, x_51, x_1, x_55, x_128, x_91, x_64, x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_67 = x_130;
x_68 = x_131;
goto block_77;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_66);
lean_dec(x_64);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
x_17 = x_135;
goto block_47;
}
}
}
else
{
uint8_t x_136; lean_object* x_137; lean_object* x_138; 
x_136 = l_Lean_ImportM_runCoreM___rarg___closed__9;
x_137 = lean_box(0);
lean_inc(x_64);
x_138 = l_Lean_ImportM_runCoreM___rarg___lambda__1(x_48, x_136, x_51, x_1, x_55, x_137, x_91, x_64, x_94);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_67 = x_139;
x_68 = x_140;
goto block_77;
}
else
{
uint8_t x_141; 
lean_dec(x_66);
lean_dec(x_64);
x_141 = !lean_is_exclusive(x_138);
if (x_141 == 0)
{
x_17 = x_138;
goto block_47;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_138, 0);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_138);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_17 = x_144;
goto block_47;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ImportM_runCoreM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_ImportM_runCoreM___rarg___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
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
uint8_t x_4; 
x_4 = 1;
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Exception_isInterrupt(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Exception_isRuntime(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_6);
x_12 = lean_apply_4(x_2, x_8, x_3, x_4, x_9);
return x_12;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = l_Lean_Exception_isInterrupt(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isRuntime(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_apply_4(x_2, x_13, x_3, x_4, x_14);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_tryCatch___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Exception_isInterrupt(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_6);
x_11 = lean_apply_4(x_2, x_8, x_3, x_4, x_9);
return x_11;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = l_Lean_Exception_isInterrupt(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_apply_4(x_2, x_12, x_3, x_4, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_tryCatchRuntimeEx___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_tryCatchRuntimeEx___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Exception_isInterrupt(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Exception_isRuntime(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_7);
x_13 = lean_apply_4(x_3, x_9, x_4, x_5, x_10);
return x_13;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = l_Lean_Exception_isInterrupt(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Exception_isRuntime(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_apply_4(x_3, x_14, x_4, x_5, x_15);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Lean_instMonadExceptOfExceptionCoreM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instMonadExceptOfExceptionCoreM___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instMonadExceptOfExceptionCoreM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instMonadExceptOfExceptionCoreM___lambda__2), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instMonadExceptOfExceptionCoreM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instMonadExceptOfExceptionCoreM___closed__1;
x_2 = l_Lean_instMonadExceptOfExceptionCoreM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instMonadExceptOfExceptionCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instMonadExceptOfExceptionCoreM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_instMonadExceptOfExceptionCoreM___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Exception_isInterrupt(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_6);
x_11 = lean_apply_4(x_2, x_8, x_3, x_4, x_9);
return x_11;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = l_Lean_Exception_isInterrupt(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_apply_4(x_2, x_12, x_3, x_4, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionCoreM___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_3(x_1, lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_3(x_1, lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_3, lean_box(0), x_1);
x_8 = lean_apply_5(x_2, lean_box(0), x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_mapCoreM___rarg___lambda__1), 6, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mapCoreM___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 5);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_NameSet_contains(x_10, x_1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_free_object(x_5);
x_12 = lean_st_ref_take(x_3, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 5);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_14, 2);
x_20 = lean_box(0);
x_21 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_19, x_1, x_20);
lean_ctor_set(x_14, 2, x_21);
x_22 = lean_st_ref_set(x_3, x_13, x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
x_33 = lean_ctor_get(x_14, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_34 = lean_box(0);
x_35 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_33, x_1, x_34);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_13, 5, x_36);
x_37 = lean_st_ref_set(x_3, x_13, x_15);
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
x_40 = 1;
x_41 = lean_box(x_40);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
x_45 = lean_ctor_get(x_13, 2);
x_46 = lean_ctor_get(x_13, 3);
x_47 = lean_ctor_get(x_13, 4);
x_48 = lean_ctor_get(x_13, 6);
x_49 = lean_ctor_get(x_13, 7);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_50 = lean_ctor_get(x_14, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_14, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_14, 2);
lean_inc(x_52);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_53 = x_14;
} else {
 lean_dec_ref(x_14);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
x_55 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_52, x_1, x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 3, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_44);
lean_ctor_set(x_57, 2, x_45);
lean_ctor_set(x_57, 3, x_46);
lean_ctor_set(x_57, 4, x_47);
lean_ctor_set(x_57, 5, x_56);
lean_ctor_set(x_57, 6, x_48);
lean_ctor_set(x_57, 7, x_49);
x_58 = lean_st_ref_set(x_3, x_57, x_15);
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
x_61 = 1;
x_62 = lean_box(x_61);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
else
{
uint8_t x_64; lean_object* x_65; 
lean_dec(x_1);
x_64 = 0;
x_65 = lean_box(x_64);
lean_ctor_set(x_5, 0, x_65);
return x_5;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_5, 0);
x_67 = lean_ctor_get(x_5, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_5);
x_68 = lean_ctor_get(x_66, 5);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_68, 2);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_NameSet_contains(x_69, x_1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_71 = lean_st_ref_take(x_3, x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_72, 6);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 7);
lean_inc(x_81);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 lean_ctor_release(x_72, 6);
 lean_ctor_release(x_72, 7);
 x_82 = x_72;
} else {
 lean_dec_ref(x_72);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_73, 2);
lean_inc(x_85);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_86 = x_73;
} else {
 lean_dec_ref(x_73);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
x_88 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_85, x_1, x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 3, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_89, 2, x_88);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 8, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_76);
lean_ctor_set(x_90, 2, x_77);
lean_ctor_set(x_90, 3, x_78);
lean_ctor_set(x_90, 4, x_79);
lean_ctor_set(x_90, 5, x_89);
lean_ctor_set(x_90, 6, x_80);
lean_ctor_set(x_90, 7, x_81);
x_91 = lean_st_ref_set(x_3, x_90, x_74);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = 1;
x_95 = lean_box(x_94);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
else
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_1);
x_97 = 0;
x_98 = lean_box(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_67);
return x_99;
}
}
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
x_10 = l_Lean_Environment_enableRealizationsForConst(x_8, x_9, x_1, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(x_11, x_2, x_3, x_12);
lean_dec(x_2);
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
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__3;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__1;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__2;
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__3;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__4;
x_2 = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__5;
x_2 = lean_unsigned_to_nat(6713u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__3;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__6;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_traceBlock___rarg___lambda__3___closed__2;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
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
l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__1);
l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__2 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__2);
l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__3 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__3);
l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__4 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__4);
l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__5);
l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__6 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5____closed__6);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__1 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__1);
l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__2 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__2);
l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__3 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__3);
l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__4 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__4);
l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__5 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_40____closed__5);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_40_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics_threshold);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__1 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__1);
l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__2 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__2);
l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__3);
l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__4 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__4);
l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__5 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__5);
l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__6 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_80____closed__6);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_80_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_maxHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_maxHeartbeats);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__1);
l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__2 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__2);
l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__3 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__3);
l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__4 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__4);
l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__5 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__5);
l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__6 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_114____closed__6);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_114_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_async = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_async);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__1 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__1);
l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__2 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__2);
l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__3 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__3);
l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__4 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__4);
l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__5 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_153____closed__5);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_153_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_inServer = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_inServer);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__1 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__1);
l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__2 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__2);
l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__3 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__3);
l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__4 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__4);
l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__5 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__5);
l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__6 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_192____closed__6);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_192_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_internal_cmdlineSnapshots = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_internal_cmdlineSnapshots);
lean_dec_ref(res);
}l_Lean_useDiagnosticMsg___lambda__2___closed__1 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__1);
l_Lean_useDiagnosticMsg___lambda__2___closed__2 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__2);
l_Lean_useDiagnosticMsg___lambda__2___closed__3 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__3();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__3);
l_Lean_useDiagnosticMsg___lambda__2___closed__4 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__4();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__4);
l_Lean_useDiagnosticMsg___lambda__2___closed__5 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__5();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__5);
l_Lean_useDiagnosticMsg___lambda__2___closed__6 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__6();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__6);
l_Lean_useDiagnosticMsg___lambda__2___closed__7 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__7();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__7);
l_Lean_useDiagnosticMsg___lambda__2___closed__8 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__8();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__8);
l_Lean_useDiagnosticMsg___lambda__2___closed__9 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__9();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__9);
l_Lean_useDiagnosticMsg___lambda__2___closed__10 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__10();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__10);
l_Lean_useDiagnosticMsg___lambda__2___closed__11 = _init_l_Lean_useDiagnosticMsg___lambda__2___closed__11();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__2___closed__11);
l_Lean_useDiagnosticMsg___lambda__3___closed__1 = _init_l_Lean_useDiagnosticMsg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__3___closed__1);
l_Lean_useDiagnosticMsg___lambda__3___closed__2 = _init_l_Lean_useDiagnosticMsg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__3___closed__2);
l_Lean_useDiagnosticMsg___lambda__3___closed__3 = _init_l_Lean_useDiagnosticMsg___lambda__3___closed__3();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lambda__3___closed__3);
l_Lean_useDiagnosticMsg___closed__1 = _init_l_Lean_useDiagnosticMsg___closed__1();
lean_mark_persistent(l_Lean_useDiagnosticMsg___closed__1);
l_Lean_useDiagnosticMsg___closed__2 = _init_l_Lean_useDiagnosticMsg___closed__2();
lean_mark_persistent(l_Lean_useDiagnosticMsg___closed__2);
l_Lean_useDiagnosticMsg___closed__3 = _init_l_Lean_useDiagnosticMsg___closed__3();
lean_mark_persistent(l_Lean_useDiagnosticMsg___closed__3);
l_Lean_useDiagnosticMsg = _init_l_Lean_useDiagnosticMsg();
lean_mark_persistent(l_Lean_useDiagnosticMsg);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__1 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__1();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__1);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__2 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__2();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__2);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__3 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__3();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__3);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__4 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__4();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__4);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__5 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__5();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__5);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__6 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__6();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__6);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__7 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__7();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__7);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__8 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__8();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__8);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__9 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__9();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__9);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__10 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__10();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__10);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__11 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__11();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__11);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__12 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__12();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__12);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__13 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__13();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__13);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__14 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__14();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__14);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__15 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__15();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263____closed__15);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Core_getMaxHeartbeats___closed__1 = _init_l_Lean_Core_getMaxHeartbeats___closed__1();
lean_mark_persistent(l_Lean_Core_getMaxHeartbeats___closed__1);
l_Lean_Core_instInhabitedCache___closed__1 = _init_l_Lean_Core_instInhabitedCache___closed__1();
lean_mark_persistent(l_Lean_Core_instInhabitedCache___closed__1);
l_Lean_Core_instInhabitedCache___closed__2 = _init_l_Lean_Core_instInhabitedCache___closed__2();
lean_mark_persistent(l_Lean_Core_instInhabitedCache___closed__2);
l_Lean_Core_instInhabitedCache___closed__3 = _init_l_Lean_Core_instInhabitedCache___closed__3();
lean_mark_persistent(l_Lean_Core_instInhabitedCache___closed__3);
l_Lean_Core_instInhabitedCache = _init_l_Lean_Core_instInhabitedCache();
lean_mark_persistent(l_Lean_Core_instInhabitedCache);
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
l_Lean_Core_instMonadCoreM___closed__7 = _init_l_Lean_Core_instMonadCoreM___closed__7();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__7);
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
l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1 = _init_l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadWithOptionsCoreM___rarg___lambda__1___closed__1);
l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1 = _init_l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___rarg___closed__1);
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
l_Lean_Core_instMonadInfoTreeCoreM___closed__1 = _init_l_Lean_Core_instMonadInfoTreeCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadInfoTreeCoreM___closed__1);
l_Lean_Core_instMonadInfoTreeCoreM___closed__2 = _init_l_Lean_Core_instMonadInfoTreeCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadInfoTreeCoreM___closed__2);
l_Lean_Core_instMonadInfoTreeCoreM___closed__3 = _init_l_Lean_Core_instMonadInfoTreeCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadInfoTreeCoreM___closed__3);
l_Lean_Core_instMonadInfoTreeCoreM = _init_l_Lean_Core_instMonadInfoTreeCoreM();
lean_mark_persistent(l_Lean_Core_instMonadInfoTreeCoreM);
l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__1();
l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Core_instantiateTypeLevelParams___spec__2___closed__3);
l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__1 = _init_l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__1);
l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__2 = _init_l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__2);
l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3 = _init_l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Core_instantiateValueLevelParams___lambda__2___closed__3);
l_Lean_Core_instMonadTraceCoreM___closed__1 = _init_l_Lean_Core_instMonadTraceCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM___closed__1);
l_Lean_Core_instMonadTraceCoreM___closed__2 = _init_l_Lean_Core_instMonadTraceCoreM___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM___closed__2);
l_Lean_Core_instMonadTraceCoreM___closed__3 = _init_l_Lean_Core_instMonadTraceCoreM___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM___closed__3);
l_Lean_Core_instMonadTraceCoreM___closed__4 = _init_l_Lean_Core_instMonadTraceCoreM___closed__4();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM___closed__4);
l_Lean_Core_instMonadTraceCoreM = _init_l_Lean_Core_instMonadTraceCoreM();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM);
l_Lean_Core_CoreM_toIO___rarg___closed__1 = _init_l_Lean_Core_CoreM_toIO___rarg___closed__1();
lean_mark_persistent(l_Lean_Core_CoreM_toIO___rarg___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Core_withIncRecDepth___spec__1___rarg___closed__6);
l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__1 = _init_l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__1);
l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__2 = _init_l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_throwInterruptException___at_Lean_Core_checkInterrupted___spec__1___rarg___closed__2);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__1 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__1();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__1);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__2 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__2();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__2);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__3 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__3();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__3);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__4 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__4();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__4);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__5 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__5();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__5);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__6 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__6();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986____closed__6);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_debug_moduleNameAtTimeout = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_debug_moduleNameAtTimeout);
lean_dec_ref(res);
}l_Lean_Core_throwMaxHeartbeat___closed__1 = _init_l_Lean_Core_throwMaxHeartbeat___closed__1();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__1);
l_Lean_Core_throwMaxHeartbeat___closed__2 = _init_l_Lean_Core_throwMaxHeartbeat___closed__2();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__2);
l_Lean_Core_throwMaxHeartbeat___closed__3 = _init_l_Lean_Core_throwMaxHeartbeat___closed__3();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__3);
l_Lean_Core_throwMaxHeartbeat___closed__4 = _init_l_Lean_Core_throwMaxHeartbeat___closed__4();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__4);
l_Lean_Core_throwMaxHeartbeat___closed__5 = _init_l_Lean_Core_throwMaxHeartbeat___closed__5();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__5);
l_Lean_Core_throwMaxHeartbeat___closed__6 = _init_l_Lean_Core_throwMaxHeartbeat___closed__6();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__6);
l_Lean_Core_throwMaxHeartbeat___closed__7 = _init_l_Lean_Core_throwMaxHeartbeat___closed__7();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__7);
l_Lean_Core_throwMaxHeartbeat___closed__8 = _init_l_Lean_Core_throwMaxHeartbeat___closed__8();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__8);
l_Lean_Core_throwMaxHeartbeat___closed__9 = _init_l_Lean_Core_throwMaxHeartbeat___closed__9();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__9);
l_Lean_Core_throwMaxHeartbeat___closed__10 = _init_l_Lean_Core_throwMaxHeartbeat___closed__10();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__10);
l_Lean_Core_throwMaxHeartbeat___closed__11 = _init_l_Lean_Core_throwMaxHeartbeat___closed__11();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__11);
l_Lean_Core_throwMaxHeartbeat___closed__12 = _init_l_Lean_Core_throwMaxHeartbeat___closed__12();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__12);
l_Lean_Core_throwMaxHeartbeat___closed__13 = _init_l_Lean_Core_throwMaxHeartbeat___closed__13();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__13);
l_Lean_Core_throwMaxHeartbeat___closed__14 = _init_l_Lean_Core_throwMaxHeartbeat___closed__14();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___closed__14);
l_Lean_Core_resetMessageLog___closed__1 = _init_l_Lean_Core_resetMessageLog___closed__1();
lean_mark_persistent(l_Lean_Core_resetMessageLog___closed__1);
l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1 = _init_l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1();
lean_mark_persistent(l_Lean_Core_getAndEmptySnapshotTasks___rarg___closed__1);
l_Lean_Core_instMonadLogCoreM___lambda__5___closed__1 = _init_l_Lean_Core_instMonadLogCoreM___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___lambda__5___closed__1);
l_Lean_Core_instMonadLogCoreM___lambda__5___closed__2 = _init_l_Lean_Core_instMonadLogCoreM___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___lambda__5___closed__2);
l_Lean_Core_instMonadLogCoreM___lambda__5___closed__3 = _init_l_Lean_Core_instMonadLogCoreM___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___lambda__5___closed__3);
l_Lean_Core_instMonadLogCoreM___lambda__5___closed__4 = _init_l_Lean_Core_instMonadLogCoreM___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___lambda__5___closed__4);
l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1 = _init_l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM___lambda__6___closed__1);
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
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__1 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__1();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__1);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__2 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__2();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__2);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__3 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__3();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__3);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__4 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__4();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__4);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__5 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__5();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__5);
l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__6 = _init_l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__6();
lean_mark_persistent(l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937____closed__6);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_stderrAsMessages = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_stderrAsMessages);
lean_dec_ref(res);
}l___auto____x40_Lean_CoreM___hyg_3975____closed__1 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__1();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__1);
l___auto____x40_Lean_CoreM___hyg_3975____closed__2 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__2();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__2);
l___auto____x40_Lean_CoreM___hyg_3975____closed__3 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__3();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__3);
l___auto____x40_Lean_CoreM___hyg_3975____closed__4 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__4();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__4);
l___auto____x40_Lean_CoreM___hyg_3975____closed__5 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__5();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__5);
l___auto____x40_Lean_CoreM___hyg_3975____closed__6 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__6();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__6);
l___auto____x40_Lean_CoreM___hyg_3975____closed__7 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__7();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__7);
l___auto____x40_Lean_CoreM___hyg_3975____closed__8 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__8();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__8);
l___auto____x40_Lean_CoreM___hyg_3975____closed__9 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__9();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__9);
l___auto____x40_Lean_CoreM___hyg_3975____closed__10 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__10();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__10);
l___auto____x40_Lean_CoreM___hyg_3975____closed__11 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__11();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__11);
l___auto____x40_Lean_CoreM___hyg_3975____closed__12 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__12();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__12);
l___auto____x40_Lean_CoreM___hyg_3975____closed__13 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__13();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__13);
l___auto____x40_Lean_CoreM___hyg_3975____closed__14 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__14();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__14);
l___auto____x40_Lean_CoreM___hyg_3975____closed__15 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__15();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__15);
l___auto____x40_Lean_CoreM___hyg_3975____closed__16 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__16();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__16);
l___auto____x40_Lean_CoreM___hyg_3975____closed__17 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__17();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__17);
l___auto____x40_Lean_CoreM___hyg_3975____closed__18 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__18();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__18);
l___auto____x40_Lean_CoreM___hyg_3975____closed__19 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__19();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__19);
l___auto____x40_Lean_CoreM___hyg_3975____closed__20 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__20();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__20);
l___auto____x40_Lean_CoreM___hyg_3975____closed__21 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__21();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__21);
l___auto____x40_Lean_CoreM___hyg_3975____closed__22 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__22();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__22);
l___auto____x40_Lean_CoreM___hyg_3975____closed__23 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__23();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__23);
l___auto____x40_Lean_CoreM___hyg_3975____closed__24 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__24();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__24);
l___auto____x40_Lean_CoreM___hyg_3975____closed__25 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__25();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__25);
l___auto____x40_Lean_CoreM___hyg_3975____closed__26 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__26();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__26);
l___auto____x40_Lean_CoreM___hyg_3975____closed__27 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__27();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__27);
l___auto____x40_Lean_CoreM___hyg_3975____closed__28 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__28();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__28);
l___auto____x40_Lean_CoreM___hyg_3975____closed__29 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__29();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__29);
l___auto____x40_Lean_CoreM___hyg_3975____closed__30 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__30();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__30);
l___auto____x40_Lean_CoreM___hyg_3975____closed__31 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__31();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__31);
l___auto____x40_Lean_CoreM___hyg_3975____closed__32 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__32();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__32);
l___auto____x40_Lean_CoreM___hyg_3975____closed__33 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__33();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__33);
l___auto____x40_Lean_CoreM___hyg_3975____closed__34 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__34();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__34);
l___auto____x40_Lean_CoreM___hyg_3975____closed__35 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__35();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__35);
l___auto____x40_Lean_CoreM___hyg_3975____closed__36 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__36();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__36);
l___auto____x40_Lean_CoreM___hyg_3975____closed__37 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__37();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__37);
l___auto____x40_Lean_CoreM___hyg_3975____closed__38 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__38();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__38);
l___auto____x40_Lean_CoreM___hyg_3975____closed__39 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__39();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__39);
l___auto____x40_Lean_CoreM___hyg_3975____closed__40 = _init_l___auto____x40_Lean_CoreM___hyg_3975____closed__40();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975____closed__40);
l___auto____x40_Lean_CoreM___hyg_3975_ = _init_l___auto____x40_Lean_CoreM___hyg_3975_();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975_);
l___auto____x40_Lean_CoreM___hyg_4116_ = _init_l___auto____x40_Lean_CoreM___hyg_4116_();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_4116_);
l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__2___closed__1();
l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__1);
l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__3___closed__2);
l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__1);
l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__2);
l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3 = _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__3);
l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__4 = _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__4();
l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5 = _init_l_Lean_withTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__1___lambda__4___closed__5();
l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Core_wrapAsyncAsSnapshot___spec__12___closed__2);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__1 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__1();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__1);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__2 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__2();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__2);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__3 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__3();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__3);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__4 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__4();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__4);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__5 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__5();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__5);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__6 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__6();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__6);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__7 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__7();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__7);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__8 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__8();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___lambda__1___closed__8);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__1 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__1();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__1);
l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__2 = _init_l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__2();
lean_mark_persistent(l_Lean_addTraceAsMessages___at_Lean_Core_wrapAsyncAsSnapshot___spec__6___closed__2);
l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___closed__1 = _init_l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_Core_wrapAsyncAsSnapshot___spec__14___closed__1);
l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__1);
l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__2);
l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__3);
l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__4);
l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Core_wrapAsyncAsSnapshot___spec__15___closed__5);
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2___closed__1 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__2___closed__1);
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__3___closed__1 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__3___closed__1);
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__1 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__1);
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__2 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__2();
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__3 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__3);
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__4 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__4);
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__5 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__5);
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__6 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__6();
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__7 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__7);
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__8 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__8);
l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__9 = _init_l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___rarg___lambda__4___closed__9);
l_Lean_mkArrow___closed__1 = _init_l_Lean_mkArrow___closed__1();
lean_mark_persistent(l_Lean_mkArrow___closed__1);
l_Lean_mkArrow___closed__2 = _init_l_Lean_mkArrow___closed__2();
lean_mark_persistent(l_Lean_mkArrow___closed__2);
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
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__29 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__29();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__29);
l___private_Lean_CoreM_0__Lean_supportedRecursors = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors);
l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1 = _init_l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1();
lean_mark_persistent(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1);
l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2 = _init_l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2();
lean_mark_persistent(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2);
l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3 = _init_l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3();
lean_mark_persistent(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3);
l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4 = _init_l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4();
lean_mark_persistent(l_List_foldlM___at___private_Lean_CoreM_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4);
l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__1 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__1);
l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__2 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__2);
l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__3 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__3);
l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__4 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__4);
l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__5 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__5);
l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__6 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_5018____closed__6);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_5018_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_compiler_enableNew = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_compiler_enableNew);
lean_dec_ref(res);
}l_Lean_traceBlock___rarg___lambda__2___closed__1 = _init_l_Lean_traceBlock___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_traceBlock___rarg___lambda__2___closed__1);
l_Lean_traceBlock___rarg___lambda__3___closed__1 = _init_l_Lean_traceBlock___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_traceBlock___rarg___lambda__3___closed__1);
l_Lean_traceBlock___rarg___lambda__3___closed__2 = _init_l_Lean_traceBlock___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_traceBlock___rarg___lambda__3___closed__2);
l_Lean_compileDecls_doCompile___lambda__1___closed__1 = _init_l_Lean_compileDecls_doCompile___lambda__1___closed__1();
lean_mark_persistent(l_Lean_compileDecls_doCompile___lambda__1___closed__1);
l_Lean_compileDecls_doCompile___lambda__1___closed__2 = _init_l_Lean_compileDecls_doCompile___lambda__1___closed__2();
lean_mark_persistent(l_Lean_compileDecls_doCompile___lambda__1___closed__2);
l_Lean_compileDecls_doCompile___lambda__4___closed__1 = _init_l_Lean_compileDecls_doCompile___lambda__4___closed__1();
lean_mark_persistent(l_Lean_compileDecls_doCompile___lambda__4___closed__1);
l_Lean_compileDecls_doCompile___lambda__4___closed__2 = _init_l_Lean_compileDecls_doCompile___lambda__4___closed__2();
lean_mark_persistent(l_Lean_compileDecls_doCompile___lambda__4___closed__2);
l_Lean_compileDecls___lambda__2___closed__1 = _init_l_Lean_compileDecls___lambda__2___closed__1();
lean_mark_persistent(l_Lean_compileDecls___lambda__2___closed__1);
l_Lean_compileDecls___lambda__2___closed__2 = _init_l_Lean_compileDecls___lambda__2___closed__2();
lean_mark_persistent(l_Lean_compileDecls___lambda__2___closed__2);
l_Lean_compileDecls___lambda__2___closed__3 = _init_l_Lean_compileDecls___lambda__2___closed__3();
lean_mark_persistent(l_Lean_compileDecls___lambda__2___closed__3);
l_Lean_compileDecls___closed__1 = _init_l_Lean_compileDecls___closed__1();
lean_mark_persistent(l_Lean_compileDecls___closed__1);
l_Lean_compileDecls___closed__2 = _init_l_Lean_compileDecls___closed__2();
lean_mark_persistent(l_Lean_compileDecls___closed__2);
l_Lean_ImportM_runCoreM___rarg___closed__1 = _init_l_Lean_ImportM_runCoreM___rarg___closed__1();
lean_mark_persistent(l_Lean_ImportM_runCoreM___rarg___closed__1);
l_Lean_ImportM_runCoreM___rarg___closed__2 = _init_l_Lean_ImportM_runCoreM___rarg___closed__2();
lean_mark_persistent(l_Lean_ImportM_runCoreM___rarg___closed__2);
l_Lean_ImportM_runCoreM___rarg___closed__3 = _init_l_Lean_ImportM_runCoreM___rarg___closed__3();
lean_mark_persistent(l_Lean_ImportM_runCoreM___rarg___closed__3);
l_Lean_ImportM_runCoreM___rarg___closed__4 = _init_l_Lean_ImportM_runCoreM___rarg___closed__4();
lean_mark_persistent(l_Lean_ImportM_runCoreM___rarg___closed__4);
l_Lean_ImportM_runCoreM___rarg___closed__5 = _init_l_Lean_ImportM_runCoreM___rarg___closed__5();
lean_mark_persistent(l_Lean_ImportM_runCoreM___rarg___closed__5);
l_Lean_ImportM_runCoreM___rarg___closed__6 = _init_l_Lean_ImportM_runCoreM___rarg___closed__6();
lean_mark_persistent(l_Lean_ImportM_runCoreM___rarg___closed__6);
l_Lean_ImportM_runCoreM___rarg___closed__7 = _init_l_Lean_ImportM_runCoreM___rarg___closed__7();
lean_mark_persistent(l_Lean_ImportM_runCoreM___rarg___closed__7);
l_Lean_ImportM_runCoreM___rarg___closed__8 = _init_l_Lean_ImportM_runCoreM___rarg___closed__8();
lean_mark_persistent(l_Lean_ImportM_runCoreM___rarg___closed__8);
l_Lean_ImportM_runCoreM___rarg___closed__9 = _init_l_Lean_ImportM_runCoreM___rarg___closed__9();
l_Lean_instMonadExceptOfExceptionCoreM___closed__1 = _init_l_Lean_instMonadExceptOfExceptionCoreM___closed__1();
lean_mark_persistent(l_Lean_instMonadExceptOfExceptionCoreM___closed__1);
l_Lean_instMonadExceptOfExceptionCoreM___closed__2 = _init_l_Lean_instMonadExceptOfExceptionCoreM___closed__2();
lean_mark_persistent(l_Lean_instMonadExceptOfExceptionCoreM___closed__2);
l_Lean_instMonadExceptOfExceptionCoreM___closed__3 = _init_l_Lean_instMonadExceptOfExceptionCoreM___closed__3();
lean_mark_persistent(l_Lean_instMonadExceptOfExceptionCoreM___closed__3);
l_Lean_instMonadExceptOfExceptionCoreM = _init_l_Lean_instMonadExceptOfExceptionCoreM();
lean_mark_persistent(l_Lean_instMonadExceptOfExceptionCoreM);
l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__1 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__1);
l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__2 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__2);
l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__3 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__3);
l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__4 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__4);
l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__5 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__5);
l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__6 = _init_l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_CoreM___hyg_6713____closed__6);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_6713_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
