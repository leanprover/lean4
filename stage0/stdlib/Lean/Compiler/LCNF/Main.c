// Lean compiler output
// Module: Lean.Compiler.LCNF.Main
// Imports: Lean.Compiler.Options Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.Passes Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.ToDecl Lean.Compiler.LCNF.Check Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.CSE
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
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__19;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
uint8_t lean_is_matcher(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4;
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3;
lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_profiler;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_useHearbeats;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_compile___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__23;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__13;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__16;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__15;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__4;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__5;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__1;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__1;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__7;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassManager_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassManager_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEq;
extern lean_object* l_Lean_casesOnSuffix;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_checkpoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__21;
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPassManager___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__9;
lean_object* l_Lean_profileitM___at_Lean_addDecl___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_main___lambda__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_withTraceNode___at_Lean_addDecl___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_lcnf_compile_decls(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__24;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_compile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__15;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__20;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16;
static lean_object* l_Lean_Compiler_LCNF_showDecl___closed__1;
lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__8;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__22;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7;
lean_object* l_Lean_Compiler_LCNF_main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__10;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__11;
lean_object* l_Lean_Compiler_LCNF_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
lean_object* l_Lean_Compiler_LCNF_main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__23;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_withPhase___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2;
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(lean_object*, uint8_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1;
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__1;
lean_object* l_Lean_Compiler_LCNF_markRecDecls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2;
lean_object* l_Lean_Compiler_LCNF_showDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__16;
static lean_object* l_Lean_Compiler_LCNF_compile___closed__2;
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10;
lean_object* l_panic___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__18;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_check;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1;
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__17;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__22;
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414_(lean_object*);
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__26;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6;
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
extern lean_object* l_Lean_Expr_instHashable;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3(lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__4;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__6;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_checkpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_size(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
static lean_object* l_Lean_Compiler_LCNF_showDecl___closed__2;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_showDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19;
extern lean_object* l_Lean_trace_profiler;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_main___closed__1;
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__14;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__25;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17;
uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashable___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_main___lambda__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__20;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__18;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__17;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12;
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__12;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_compileDecl___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5;
static lean_object* l_Lean_Compiler_LCNF_compile___closed__3;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__19;
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__2;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__21;
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___closed__1;
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_11 = l_Lean_Meta_isProp(x_10, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_isTypeFormerType(x_10, x_2, x_3, x_4, x_5, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_is_matcher(x_8, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_is_matcher(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___closed__1;
x_8 = l_Lean_casesOnSuffix;
x_9 = l_Lean_isAuxRecursorWithSuffix(x_1, x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_apply_4(x_7, x_10, x_4, x_5, x_6);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_7 = l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1(x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2(x_2, x_1, x_11, x_4, x_5, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; 
x_7 = 2;
lean_inc(x_1);
x_8 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_2, x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3(x_1, x_2, x_9, x_4, x_5, x_6);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_isExtern(x_10, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_6);
x_12 = lean_box(0);
x_13 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4(x_1, x_10, x_12, x_3, x_4, x_9);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_isExtern(x_18, x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4(x_1, x_18, x_20, x_3, x_4, x_17);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_getDeclInfo_x3f(x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lean_ConstantInfo_hasValue(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_6);
x_23 = lean_box(0);
x_24 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5(x_1, x_23, x_3, x_4, x_17);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec(x_7);
x_27 = l_Lean_ConstantInfo_hasValue(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5(x_1, x_31, x_3, x_4, x_25);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_2);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_2);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_4);
lean_ctor_set_uint8(x_5, 12, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5;
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
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_1);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashable___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEq;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashable;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__21;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__15;
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__17;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__18;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__22;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__24;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__23;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
x_5 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__25;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__26;
x_6 = lean_st_mk_ref(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(x_1, x_9, x_7, x_2, x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_7, x_12);
lean_dec(x_7);
x_14 = lean_unbox(x_11);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6(x_1, x_16, x_2, x_3, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_compiler_check;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1;
x_10 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Decl_check(x_1, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("size: ", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_8, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_dec(x_13);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1;
x_15 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_14);
lean_ctor_set(x_8, 4, x_15);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*12, x_2);
lean_inc(x_3);
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_3, x_4, x_5, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_20, x_4, x_5, x_8, x_9, x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_25 = l_Lean_Compiler_LCNF_ppDecl_x27(x_6, x_8, x_9, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Compiler_LCNF_Decl_size(x_6);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_MessageData_ofFormat(x_30);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_31);
lean_ctor_set(x_16, 0, x_32);
x_33 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_26);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_3, x_38, x_4, x_5, x_8, x_9, x_27);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_40, x_4, x_5, x_8, x_9, x_41);
lean_dec(x_40);
return x_42;
}
else
{
uint8_t x_43; 
lean_free_object(x_16);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_25, 0);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_25);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_48 = l_Lean_Compiler_LCNF_ppDecl_x27(x_6, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Compiler_LCNF_Decl_size(x_6);
x_52 = l___private_Init_Data_Repr_0__Nat_reprFast(x_51);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_MessageData_ofFormat(x_49);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_3, x_62, x_4, x_5, x_8, x_9, x_50);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_64, x_4, x_5, x_8, x_9, x_65);
lean_dec(x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = lean_ctor_get(x_48, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_69 = x_48;
} else {
 lean_dec_ref(x_48);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_71 = lean_ctor_get(x_8, 0);
x_72 = lean_ctor_get(x_8, 1);
x_73 = lean_ctor_get(x_8, 3);
x_74 = lean_ctor_get(x_8, 5);
x_75 = lean_ctor_get(x_8, 6);
x_76 = lean_ctor_get(x_8, 7);
x_77 = lean_ctor_get(x_8, 8);
x_78 = lean_ctor_get(x_8, 9);
x_79 = lean_ctor_get(x_8, 10);
x_80 = lean_ctor_get(x_8, 11);
x_81 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_8);
x_82 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1;
x_83 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_82);
x_84 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_84, 0, x_71);
lean_ctor_set(x_84, 1, x_72);
lean_ctor_set(x_84, 2, x_1);
lean_ctor_set(x_84, 3, x_73);
lean_ctor_set(x_84, 4, x_83);
lean_ctor_set(x_84, 5, x_74);
lean_ctor_set(x_84, 6, x_75);
lean_ctor_set(x_84, 7, x_76);
lean_ctor_set(x_84, 8, x_77);
lean_ctor_set(x_84, 9, x_78);
lean_ctor_set(x_84, 10, x_79);
lean_ctor_set(x_84, 11, x_80);
lean_ctor_set_uint8(x_84, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_84, sizeof(void*)*12 + 1, x_81);
lean_inc(x_3);
x_85 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_3, x_4, x_5, x_84, x_9, x_10);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_3);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_box(0);
x_90 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_89, x_4, x_5, x_84, x_9, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
 x_92 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_84);
lean_inc(x_6);
x_93 = l_Lean_Compiler_LCNF_ppDecl_x27(x_6, x_84, x_9, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Compiler_LCNF_Decl_size(x_6);
x_97 = l___private_Init_Data_Repr_0__Nat_reprFast(x_96);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Lean_MessageData_ofFormat(x_98);
x_100 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
if (lean_is_scalar(x_92)) {
 x_101 = lean_alloc_ctor(7, 2, 0);
} else {
 x_101 = x_92;
 lean_ctor_set_tag(x_101, 7);
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_MessageData_ofFormat(x_94);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_3, x_107, x_4, x_5, x_84, x_9, x_95);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_109, x_4, x_5, x_84, x_9, x_110);
lean_dec(x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_92);
lean_dec(x_84);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_ctor_get(x_93, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_93, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_114 = x_93;
} else {
 lean_dec_ref(x_93);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pp", 2);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("motives", 7);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pi", 2);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2;
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6;
x_13 = 0;
x_14 = l_Lean_KVMap_setBool(x_11, x_12, x_13);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7;
x_16 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_14, x_15);
x_17 = lean_st_ref_get(x_7, x_8);
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
uint8_t x_79; 
x_79 = 1;
x_22 = x_79;
goto block_78;
}
else
{
x_22 = x_13;
goto block_78;
}
}
else
{
if (x_16 == 0)
{
x_22 = x_13;
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = 1;
x_22 = x_80;
goto block_78;
}
}
block_78:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_st_ref_take(x_7, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 4);
lean_dec(x_28);
x_29 = l_Lean_Kernel_enableDiag(x_27, x_16);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8;
lean_ctor_set(x_24, 4, x_30);
lean_ctor_set(x_24, 0, x_29);
x_31 = lean_st_ref_set(x_7, x_24, x_25);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(x_14, x_16, x_10, x_4, x_5, x_2, x_33, x_6, x_7, x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 0);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_24, 0);
x_46 = lean_ctor_get(x_24, 1);
x_47 = lean_ctor_get(x_24, 2);
x_48 = lean_ctor_get(x_24, 3);
x_49 = lean_ctor_get(x_24, 5);
x_50 = lean_ctor_get(x_24, 6);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_24);
x_51 = l_Lean_Kernel_enableDiag(x_45, x_16);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8;
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set(x_53, 2, x_47);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_49);
lean_ctor_set(x_53, 6, x_50);
x_54 = lean_st_ref_set(x_7, x_53, x_25);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(x_14, x_16, x_10, x_4, x_5, x_2, x_56, x_6, x_7, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_64 = x_57;
} else {
 lean_dec_ref(x_57);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(x_14, x_16, x_10, x_4, x_5, x_2, x_66, x_6, x_7, x_19);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
x_70 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_67);
if (x_74 == 0)
{
return x_67;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_67, 0);
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_67);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stat", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
x_13 = lean_array_uget(x_2, x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_14, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(x_1, x_13, x_19, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_5 = x_29;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_38 = lean_ctor_get(x_15, 1);
x_39 = lean_ctor_get(x_15, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
x_41 = l_Lean_MessageData_ofName(x_40);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_41);
lean_ctor_set(x_15, 0, x_42);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Compiler_LCNF_Decl_size(x_13);
x_46 = l___private_Init_Data_Repr_0__Nat_reprFast(x_45);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_MessageData_ofFormat(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
x_51 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_14, x_50, x_6, x_7, x_8, x_9, x_38);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_54 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(x_1, x_13, x_52, x_6, x_7, x_8, x_9, x_53);
lean_dec(x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; 
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
lean_dec(x_55);
x_64 = 1;
x_65 = lean_usize_add(x_4, x_64);
x_4 = x_65;
x_5 = x_63;
x_10 = x_62;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_54);
if (x_67 == 0)
{
return x_54;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_54, 0);
x_69 = lean_ctor_get(x_54, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_54);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_71 = lean_ctor_get(x_15, 1);
lean_inc(x_71);
lean_dec(x_15);
x_72 = lean_ctor_get(x_13, 0);
lean_inc(x_72);
x_73 = l_Lean_MessageData_ofName(x_72);
x_74 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Compiler_LCNF_Decl_size(x_13);
x_79 = l___private_Init_Data_Repr_0__Nat_reprFast(x_78);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = l_Lean_MessageData_ofFormat(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
x_84 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_14, x_83, x_6, x_7, x_8, x_9, x_71);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_87 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(x_1, x_13, x_85, x_6, x_7, x_8, x_9, x_86);
lean_dec(x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
lean_dec(x_88);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; size_t x_95; size_t x_96; 
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_ctor_get(x_88, 0);
lean_inc(x_94);
lean_dec(x_88);
x_95 = 1;
x_96 = lean_usize_add(x_4, x_95);
x_4 = x_96;
x_5 = x_94;
x_10 = x_93;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_100 = x_87;
} else {
 lean_dec_ref(x_87);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_checkpoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1(x_1, x_2, x_9, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_5, 2);
lean_inc(x_16);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1;
x_18 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_19; 
lean_free_object(x_12);
x_19 = l_Lean_Compiler_LCNF_checkDeadLocalDecls(x_2, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1;
x_23 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Compiler_LCNF_checkDeadLocalDecls(x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Compiler_LCNF_checkpoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_checkpoint(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Compiler_LCNF_toDecl(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_st_ref_take(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 3);
lean_dec(x_11);
x_12 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
lean_ctor_set(x_8, 3, x_12);
x_13 = lean_st_ref_set(x_1, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 4);
x_22 = lean_ctor_get(x_8, 5);
x_23 = lean_ctor_get(x_8, 6);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_24 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set(x_25, 6, x_23);
x_26 = lean_st_ref_set(x_1, x_25, x_9);
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
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_10 = lean_ctor_get(x_7, 2);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_PersistentArray_toArray___rarg(x_14);
lean_dec(x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(x_17, x_18, x_15);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_st_ref_get(x_8, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_6, x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_29);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
lean_inc(x_10);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_10);
lean_ctor_set_tag(x_25, 3);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 0, x_32);
x_33 = lean_st_ref_take(x_8, x_28);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_33, 1);
x_38 = lean_ctor_get(x_35, 3);
lean_dec(x_38);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 0, x_3);
x_39 = l_Lean_PersistentArray_push___rarg(x_1, x_33);
lean_ctor_set(x_35, 3, x_39);
x_40 = lean_st_ref_set(x_8, x_35, x_37);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_47 = lean_ctor_get(x_33, 1);
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
x_50 = lean_ctor_get(x_35, 2);
x_51 = lean_ctor_get(x_35, 4);
x_52 = lean_ctor_get(x_35, 5);
x_53 = lean_ctor_get(x_35, 6);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 0, x_3);
x_54 = l_Lean_PersistentArray_push___rarg(x_1, x_33);
x_55 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_49);
lean_ctor_set(x_55, 2, x_50);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_52);
lean_ctor_set(x_55, 6, x_53);
x_56 = lean_st_ref_set(x_8, x_55, x_47);
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
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_61 = lean_ctor_get(x_33, 0);
x_62 = lean_ctor_get(x_33, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_33);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 6);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 lean_ctor_release(x_61, 6);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_25);
x_71 = l_Lean_PersistentArray_push___rarg(x_1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 7, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_64);
lean_ctor_set(x_72, 2, x_65);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_66);
lean_ctor_set(x_72, 5, x_67);
lean_ctor_set(x_72, 6, x_68);
x_73 = lean_st_ref_set(x_8, x_72, x_62);
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
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_78 = lean_ctor_get(x_25, 0);
x_79 = lean_ctor_get(x_25, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_25);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_80);
lean_dec(x_80);
x_82 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
lean_inc(x_10);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_24);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_10);
x_84 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_20);
x_85 = lean_st_ref_take(x_8, x_79);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 4);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 5);
lean_inc(x_93);
x_94 = lean_ctor_get(x_86, 6);
lean_inc(x_94);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 lean_ctor_release(x_86, 6);
 x_95 = x_86;
} else {
 lean_dec_ref(x_86);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_88;
}
lean_ctor_set(x_96, 0, x_3);
lean_ctor_set(x_96, 1, x_84);
x_97 = l_Lean_PersistentArray_push___rarg(x_1, x_96);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(0, 7, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_89);
lean_ctor_set(x_98, 1, x_90);
lean_ctor_set(x_98, 2, x_91);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set(x_98, 4, x_92);
lean_ctor_set(x_98, 5, x_93);
lean_ctor_set(x_98, 6, x_94);
x_99 = lean_st_ref_set(x_8, x_98, x_87);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__4(x_1, x_5, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_4, x_7, x_8, x_9, x_10, x_13);
return x_14;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_profiler;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, double x_9, double x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
double x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_2);
x_19 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__2;
x_20 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_7, x_19);
if (x_20 == 0)
{
if (x_8 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1(x_4, x_5, x_11, x_6, x_18, x_21, x_12, x_13, x_14, x_15, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_2);
x_24 = lean_box(0);
x_25 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1(x_4, x_5, x_11, x_6, x_23, x_24, x_12, x_13, x_14, x_15, x_16);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_2);
x_27 = lean_box(0);
x_28 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1(x_4, x_5, x_11, x_6, x_26, x_27, x_12, x_13, x_14, x_15, x_16);
return x_28;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<exception thrown while producing trace node message>", 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
x_18 = lean_apply_6(x_10, x_5, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_19, x_12, x_13, x_14, x_15, x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__2;
x_24 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_23, x_12, x_13, x_14, x_15, x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_24;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHearbeats;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__4() {
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
static double _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5() {
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___rarg(x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__1;
x_18 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_io_mono_nanos_now(x_16);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_90 = lean_apply_5(x_7, x_9, x_10, x_11, x_12, x_89);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_92);
x_95 = lean_io_mono_nanos_now(x_93);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; double x_101; double x_102; double x_103; double x_104; double x_105; lean_object* x_106; lean_object* x_107; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = 0;
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Float_ofScientific(x_88, x_99, x_100);
lean_dec(x_88);
x_102 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_103 = lean_float_div(x_101, x_102);
x_104 = l_Float_ofScientific(x_97, x_99, x_100);
lean_dec(x_97);
x_105 = lean_float_div(x_104, x_102);
x_106 = lean_box_float(x_103);
x_107 = lean_box_float(x_105);
lean_ctor_set(x_95, 1, x_107);
lean_ctor_set(x_95, 0, x_106);
lean_ctor_set(x_90, 1, x_95);
lean_ctor_set(x_90, 0, x_94);
x_19 = x_90;
x_20 = x_98;
goto block_86;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; double x_112; double x_113; double x_114; double x_115; double x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_95, 0);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_95);
x_110 = 0;
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Float_ofScientific(x_88, x_110, x_111);
lean_dec(x_88);
x_113 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_114 = lean_float_div(x_112, x_113);
x_115 = l_Float_ofScientific(x_108, x_110, x_111);
lean_dec(x_108);
x_116 = lean_float_div(x_115, x_113);
x_117 = lean_box_float(x_114);
x_118 = lean_box_float(x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_90, 1, x_119);
lean_ctor_set(x_90, 0, x_94);
x_19 = x_90;
x_20 = x_109;
goto block_86;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; double x_129; double x_130; double x_131; double x_132; double x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_120 = lean_ctor_get(x_90, 0);
x_121 = lean_ctor_get(x_90, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_90);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_120);
x_123 = lean_io_mono_nanos_now(x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = 0;
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Float_ofScientific(x_88, x_127, x_128);
lean_dec(x_88);
x_130 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_131 = lean_float_div(x_129, x_130);
x_132 = l_Float_ofScientific(x_124, x_127, x_128);
lean_dec(x_124);
x_133 = lean_float_div(x_132, x_130);
x_134 = lean_box_float(x_131);
x_135 = lean_box_float(x_133);
if (lean_is_scalar(x_126)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_126;
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_122);
lean_ctor_set(x_137, 1, x_136);
x_19 = x_137;
x_20 = x_125;
goto block_86;
}
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_90);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_90, 0);
x_140 = lean_ctor_get(x_90, 1);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_139);
x_142 = lean_io_mono_nanos_now(x_140);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; double x_148; double x_149; double x_150; double x_151; double x_152; lean_object* x_153; lean_object* x_154; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_142, 1);
x_146 = 0;
x_147 = lean_unsigned_to_nat(0u);
x_148 = l_Float_ofScientific(x_88, x_146, x_147);
lean_dec(x_88);
x_149 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_150 = lean_float_div(x_148, x_149);
x_151 = l_Float_ofScientific(x_144, x_146, x_147);
lean_dec(x_144);
x_152 = lean_float_div(x_151, x_149);
x_153 = lean_box_float(x_150);
x_154 = lean_box_float(x_152);
lean_ctor_set(x_142, 1, x_154);
lean_ctor_set(x_142, 0, x_153);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 1, x_142);
lean_ctor_set(x_90, 0, x_141);
x_19 = x_90;
x_20 = x_145;
goto block_86;
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; double x_159; double x_160; double x_161; double x_162; double x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_142, 0);
x_156 = lean_ctor_get(x_142, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_142);
x_157 = 0;
x_158 = lean_unsigned_to_nat(0u);
x_159 = l_Float_ofScientific(x_88, x_157, x_158);
lean_dec(x_88);
x_160 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_161 = lean_float_div(x_159, x_160);
x_162 = l_Float_ofScientific(x_155, x_157, x_158);
lean_dec(x_155);
x_163 = lean_float_div(x_162, x_160);
x_164 = lean_box_float(x_161);
x_165 = lean_box_float(x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 1, x_166);
lean_ctor_set(x_90, 0, x_141);
x_19 = x_90;
x_20 = x_156;
goto block_86;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; double x_176; double x_177; double x_178; double x_179; double x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_167 = lean_ctor_get(x_90, 0);
x_168 = lean_ctor_get(x_90, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_90);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_167);
x_170 = lean_io_mono_nanos_now(x_168);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = 0;
x_175 = lean_unsigned_to_nat(0u);
x_176 = l_Float_ofScientific(x_88, x_174, x_175);
lean_dec(x_88);
x_177 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_178 = lean_float_div(x_176, x_177);
x_179 = l_Float_ofScientific(x_171, x_174, x_175);
lean_dec(x_171);
x_180 = lean_float_div(x_179, x_177);
x_181 = lean_box_float(x_178);
x_182 = lean_box_float(x_180);
if (lean_is_scalar(x_173)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_173;
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_169);
lean_ctor_set(x_184, 1, x_183);
x_19 = x_184;
x_20 = x_172;
goto block_86;
}
}
block_86:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_72; uint8_t x_73; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_72 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
x_73 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_1, x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = 0;
x_25 = x_74;
goto block_71;
}
else
{
double x_75; double x_76; double x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; double x_82; double x_83; double x_84; uint8_t x_85; 
x_75 = lean_unbox_float(x_24);
x_76 = lean_unbox_float(x_23);
x_77 = lean_float_sub(x_75, x_76);
x_78 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3;
x_79 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_78);
x_80 = 0;
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Float_ofScientific(x_79, x_80, x_81);
lean_dec(x_79);
x_83 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__4;
x_84 = lean_float_div(x_82, x_83);
x_85 = lean_float_decLt(x_84, x_77);
x_25 = x_85;
goto block_71;
}
block_71:
{
if (x_6 == 0)
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_st_ref_take(x_12, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_27, 3);
x_31 = l_Lean_PersistentArray_append___rarg(x_15, x_30);
lean_dec(x_30);
lean_ctor_set(x_27, 3, x_31);
x_32 = lean_st_ref_set(x_12, x_27, x_28);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_22, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_22);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
x_45 = lean_ctor_get(x_27, 2);
x_46 = lean_ctor_get(x_27, 3);
x_47 = lean_ctor_get(x_27, 4);
x_48 = lean_ctor_get(x_27, 5);
x_49 = lean_ctor_get(x_27, 6);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_50 = l_Lean_PersistentArray_append___rarg(x_15, x_46);
lean_dec(x_46);
x_51 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_47);
lean_ctor_set(x_51, 5, x_48);
lean_ctor_set(x_51, 6, x_49);
x_52 = lean_st_ref_set(x_12, x_51, x_28);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_22, x_9, x_10, x_11, x_12, x_53);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_22);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
lean_object* x_63; double x_64; double x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_unbox_float(x_23);
lean_dec(x_23);
x_65 = lean_unbox_float(x_24);
lean_dec(x_24);
x_66 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_22, x_1, x_25, x_64, x_65, x_5, x_63, x_9, x_10, x_11, x_12, x_20);
return x_66;
}
}
else
{
lean_object* x_67; double x_68; double x_69; lean_object* x_70; 
x_67 = lean_box(0);
x_68 = lean_unbox_float(x_23);
lean_dec(x_23);
x_69 = lean_unbox_float(x_24);
lean_dec(x_24);
x_70 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_22, x_1, x_25, x_68, x_69, x_5, x_67, x_9, x_10, x_11, x_12, x_20);
return x_70;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_io_get_num_heartbeats(x_16);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_254 = lean_apply_5(x_7, x_9, x_10, x_11, x_12, x_253);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_256 = lean_ctor_get(x_254, 0);
x_257 = lean_ctor_get(x_254, 1);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_256);
x_259 = lean_io_get_num_heartbeats(x_257);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; double x_265; double x_266; lean_object* x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_259, 0);
x_262 = lean_ctor_get(x_259, 1);
x_263 = 0;
x_264 = lean_unsigned_to_nat(0u);
x_265 = l_Float_ofScientific(x_252, x_263, x_264);
lean_dec(x_252);
x_266 = l_Float_ofScientific(x_261, x_263, x_264);
lean_dec(x_261);
x_267 = lean_box_float(x_265);
x_268 = lean_box_float(x_266);
lean_ctor_set(x_259, 1, x_268);
lean_ctor_set(x_259, 0, x_267);
lean_ctor_set(x_254, 1, x_259);
lean_ctor_set(x_254, 0, x_258);
x_185 = x_254;
x_186 = x_262;
goto block_250;
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; double x_273; double x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_269 = lean_ctor_get(x_259, 0);
x_270 = lean_ctor_get(x_259, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_259);
x_271 = 0;
x_272 = lean_unsigned_to_nat(0u);
x_273 = l_Float_ofScientific(x_252, x_271, x_272);
lean_dec(x_252);
x_274 = l_Float_ofScientific(x_269, x_271, x_272);
lean_dec(x_269);
x_275 = lean_box_float(x_273);
x_276 = lean_box_float(x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
lean_ctor_set(x_254, 1, x_277);
lean_ctor_set(x_254, 0, x_258);
x_185 = x_254;
x_186 = x_270;
goto block_250;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; double x_287; double x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_278 = lean_ctor_get(x_254, 0);
x_279 = lean_ctor_get(x_254, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_254);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_278);
x_281 = lean_io_get_num_heartbeats(x_279);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_284 = x_281;
} else {
 lean_dec_ref(x_281);
 x_284 = lean_box(0);
}
x_285 = 0;
x_286 = lean_unsigned_to_nat(0u);
x_287 = l_Float_ofScientific(x_252, x_285, x_286);
lean_dec(x_252);
x_288 = l_Float_ofScientific(x_282, x_285, x_286);
lean_dec(x_282);
x_289 = lean_box_float(x_287);
x_290 = lean_box_float(x_288);
if (lean_is_scalar(x_284)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_284;
}
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_280);
lean_ctor_set(x_292, 1, x_291);
x_185 = x_292;
x_186 = x_283;
goto block_250;
}
}
else
{
uint8_t x_293; 
x_293 = !lean_is_exclusive(x_254);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_254, 0);
x_295 = lean_ctor_get(x_254, 1);
x_296 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_296, 0, x_294);
x_297 = lean_io_get_num_heartbeats(x_295);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; double x_303; double x_304; lean_object* x_305; lean_object* x_306; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_ctor_get(x_297, 1);
x_301 = 0;
x_302 = lean_unsigned_to_nat(0u);
x_303 = l_Float_ofScientific(x_252, x_301, x_302);
lean_dec(x_252);
x_304 = l_Float_ofScientific(x_299, x_301, x_302);
lean_dec(x_299);
x_305 = lean_box_float(x_303);
x_306 = lean_box_float(x_304);
lean_ctor_set(x_297, 1, x_306);
lean_ctor_set(x_297, 0, x_305);
lean_ctor_set_tag(x_254, 0);
lean_ctor_set(x_254, 1, x_297);
lean_ctor_set(x_254, 0, x_296);
x_185 = x_254;
x_186 = x_300;
goto block_250;
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; double x_311; double x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_307 = lean_ctor_get(x_297, 0);
x_308 = lean_ctor_get(x_297, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_297);
x_309 = 0;
x_310 = lean_unsigned_to_nat(0u);
x_311 = l_Float_ofScientific(x_252, x_309, x_310);
lean_dec(x_252);
x_312 = l_Float_ofScientific(x_307, x_309, x_310);
lean_dec(x_307);
x_313 = lean_box_float(x_311);
x_314 = lean_box_float(x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set_tag(x_254, 0);
lean_ctor_set(x_254, 1, x_315);
lean_ctor_set(x_254, 0, x_296);
x_185 = x_254;
x_186 = x_308;
goto block_250;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; double x_325; double x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_316 = lean_ctor_get(x_254, 0);
x_317 = lean_ctor_get(x_254, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_254);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_316);
x_319 = lean_io_get_num_heartbeats(x_317);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
x_323 = 0;
x_324 = lean_unsigned_to_nat(0u);
x_325 = l_Float_ofScientific(x_252, x_323, x_324);
lean_dec(x_252);
x_326 = l_Float_ofScientific(x_320, x_323, x_324);
lean_dec(x_320);
x_327 = lean_box_float(x_325);
x_328 = lean_box_float(x_326);
if (lean_is_scalar(x_322)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_322;
}
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_318);
lean_ctor_set(x_330, 1, x_329);
x_185 = x_330;
x_186 = x_321;
goto block_250;
}
}
block_250:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_238; uint8_t x_239; 
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_238 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
x_239 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_1, x_238);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = 0;
x_191 = x_240;
goto block_237;
}
else
{
double x_241; double x_242; double x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; double x_248; uint8_t x_249; 
x_241 = lean_unbox_float(x_190);
x_242 = lean_unbox_float(x_189);
x_243 = lean_float_sub(x_241, x_242);
x_244 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3;
x_245 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_244);
x_246 = 0;
x_247 = lean_unsigned_to_nat(0u);
x_248 = l_Float_ofScientific(x_245, x_246, x_247);
lean_dec(x_245);
x_249 = lean_float_decLt(x_248, x_243);
x_191 = x_249;
goto block_237;
}
block_237:
{
if (x_6 == 0)
{
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_192 = lean_st_ref_take(x_12, x_186);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_193, 3);
x_197 = l_Lean_PersistentArray_append___rarg(x_15, x_196);
lean_dec(x_196);
lean_ctor_set(x_193, 3, x_197);
x_198 = lean_st_ref_set(x_12, x_193, x_194);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_188, x_9, x_10, x_11, x_12, x_199);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_188);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
return x_200;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_200);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
else
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_200);
if (x_205 == 0)
{
return x_200;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_200, 0);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_200);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_209 = lean_ctor_get(x_193, 0);
x_210 = lean_ctor_get(x_193, 1);
x_211 = lean_ctor_get(x_193, 2);
x_212 = lean_ctor_get(x_193, 3);
x_213 = lean_ctor_get(x_193, 4);
x_214 = lean_ctor_get(x_193, 5);
x_215 = lean_ctor_get(x_193, 6);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_193);
x_216 = l_Lean_PersistentArray_append___rarg(x_15, x_212);
lean_dec(x_212);
x_217 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_210);
lean_ctor_set(x_217, 2, x_211);
lean_ctor_set(x_217, 3, x_216);
lean_ctor_set(x_217, 4, x_213);
lean_ctor_set(x_217, 5, x_214);
lean_ctor_set(x_217, 6, x_215);
x_218 = lean_st_ref_set(x_12, x_217, x_194);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_188, x_9, x_10, x_11, x_12, x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_188);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_227 = x_220;
} else {
 lean_dec_ref(x_220);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
else
{
lean_object* x_229; double x_230; double x_231; lean_object* x_232; 
x_229 = lean_box(0);
x_230 = lean_unbox_float(x_189);
lean_dec(x_189);
x_231 = lean_unbox_float(x_190);
lean_dec(x_190);
x_232 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_188, x_1, x_191, x_230, x_231, x_5, x_229, x_9, x_10, x_11, x_12, x_186);
return x_232;
}
}
else
{
lean_object* x_233; double x_234; double x_235; lean_object* x_236; 
x_233 = lean_box(0);
x_234 = lean_unbox_float(x_189);
lean_dec(x_189);
x_235 = lean_unbox_float(x_190);
lean_dec(x_190);
x_236 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_188, x_1, x_191, x_234, x_235, x_5, x_233, x_9, x_10, x_11, x_12, x_186);
return x_236;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_inc(x_1);
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
x_17 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = lean_unbox(x_13);
lean_dec(x_13);
x_29 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4(x_11, x_1, x_4, x_5, x_2, x_28, x_3, x_27, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_11);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = lean_unbox(x_13);
lean_dec(x_13);
x_33 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4(x_11, x_1, x_4, x_5, x_2, x_32, x_3, x_31, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_11);
return x_33;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("new compiler phase: ", 20);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", pass: ", 8);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("base", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mono", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("impure", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_MessageData_ofName(x_9);
switch (x_8) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___boxed), 7, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
x_16 = lean_apply_1(x_15, x_4);
x_17 = lean_box(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withPhase___rarg___boxed), 7, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_16);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2;
x_20 = 1;
x_21 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2(x_19, x_13, x_18, x_20, x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 1);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Lean_Compiler_LCNF_checkpoint(x_26, x_23, x_28, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; size_t x_31; size_t x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_4 = x_23;
x_9 = x_30;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 0, x_21);
x_22 = lean_st_ref_take(x_6, x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; double x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_24, 3);
x_28 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_29 = 0;
x_30 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_31 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_float(x_31, sizeof(void*)*2, x_28);
lean_ctor_set_float(x_31, sizeof(void*)*2 + 8, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 16, x_29);
x_32 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_13);
lean_ctor_set(x_33, 2, x_32);
lean_inc(x_8);
lean_ctor_set(x_22, 1, x_33);
lean_ctor_set(x_22, 0, x_8);
x_34 = l_Lean_PersistentArray_push___rarg(x_27, x_22);
lean_ctor_set(x_24, 3, x_34);
x_35 = lean_st_ref_set(x_6, x_24, x_26);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; double x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get(x_22, 1);
x_43 = lean_ctor_get(x_24, 0);
x_44 = lean_ctor_get(x_24, 1);
x_45 = lean_ctor_get(x_24, 2);
x_46 = lean_ctor_get(x_24, 3);
x_47 = lean_ctor_get(x_24, 4);
x_48 = lean_ctor_get(x_24, 5);
x_49 = lean_ctor_get(x_24, 6);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_24);
x_50 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_51 = 0;
x_52 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_53 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_float(x_53, sizeof(void*)*2, x_50);
lean_ctor_set_float(x_53, sizeof(void*)*2 + 8, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 16, x_51);
x_54 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_55 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_13);
lean_ctor_set(x_55, 2, x_54);
lean_inc(x_8);
lean_ctor_set(x_22, 1, x_55);
lean_ctor_set(x_22, 0, x_8);
x_56 = l_Lean_PersistentArray_push___rarg(x_46, x_22);
x_57 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_44);
lean_ctor_set(x_57, 2, x_45);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set(x_57, 4, x_47);
lean_ctor_set(x_57, 5, x_48);
lean_ctor_set(x_57, 6, x_49);
x_58 = lean_st_ref_set(x_6, x_57, x_42);
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
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; double x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_63 = lean_ctor_get(x_22, 0);
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_22);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 6);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 lean_ctor_release(x_63, 5);
 lean_ctor_release(x_63, 6);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_74 = 0;
x_75 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_76 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set_float(x_76, sizeof(void*)*2, x_73);
lean_ctor_set_float(x_76, sizeof(void*)*2 + 8, x_73);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 16, x_74);
x_77 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_78 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_13);
lean_ctor_set(x_78, 2, x_77);
lean_inc(x_8);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_PersistentArray_push___rarg(x_68, x_79);
if (lean_is_scalar(x_72)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_72;
}
lean_ctor_set(x_81, 0, x_65);
lean_ctor_set(x_81, 1, x_66);
lean_ctor_set(x_81, 2, x_67);
lean_ctor_set(x_81, 3, x_80);
lean_ctor_set(x_81, 4, x_69);
lean_ctor_set(x_81, 5, x_70);
lean_ctor_set(x_81, 6, x_71);
x_82 = lean_st_ref_set(x_6, x_81, x_64);
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
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; double x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_87 = lean_ctor_get(x_13, 0);
x_88 = lean_ctor_get(x_13, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_13);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_89);
lean_dec(x_89);
x_91 = lean_ctor_get(x_5, 2);
x_92 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
lean_inc(x_91);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_12);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_91);
x_94 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_2);
x_95 = lean_st_ref_take(x_6, x_88);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_96, 5);
lean_inc(x_104);
x_105 = lean_ctor_get(x_96, 6);
lean_inc(x_105);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 lean_ctor_release(x_96, 5);
 lean_ctor_release(x_96, 6);
 x_106 = x_96;
} else {
 lean_dec_ref(x_96);
 x_106 = lean_box(0);
}
x_107 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_108 = 0;
x_109 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_110 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_float(x_110, sizeof(void*)*2, x_107);
lean_ctor_set_float(x_110, sizeof(void*)*2 + 8, x_107);
lean_ctor_set_uint8(x_110, sizeof(void*)*2 + 16, x_108);
x_111 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_112 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_94);
lean_ctor_set(x_112, 2, x_111);
lean_inc(x_8);
if (lean_is_scalar(x_98)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_98;
}
lean_ctor_set(x_113, 0, x_8);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_PersistentArray_push___rarg(x_102, x_113);
if (lean_is_scalar(x_106)) {
 x_115 = lean_alloc_ctor(0, 7, 0);
} else {
 x_115 = x_106;
}
lean_ctor_set(x_115, 0, x_99);
lean_ctor_set(x_115, 1, x_100);
lean_ctor_set(x_115, 2, x_101);
lean_ctor_set(x_115, 3, x_114);
lean_ctor_set(x_115, 4, x_103);
lean_ctor_set(x_115, 5, x_104);
lean_ctor_set(x_115, 6, x_105);
x_116 = lean_st_ref_set(x_6, x_115, x_97);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Main", 23);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.PassManager.run", 34);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2;
x_3 = lean_unsigned_to_nat(82u);
x_4 = lean_unsigned_to_nat(52u);
x_5 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_13 = lean_array_uget(x_2, x_4);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = 1;
x_23 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_21, x_22, x_8, x_9, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_panic___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__15(x_26, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_14 = x_29;
x_15 = x_28;
goto block_20;
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_23, 1);
x_36 = lean_ctor_get(x_23, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_24, 0);
lean_inc(x_9);
lean_inc(x_8);
x_39 = l_Lean_Compiler_LCNF_ppDecl_x27(x_38, x_8, x_9, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_Decl_size(x_13);
lean_dec(x_13);
x_43 = l___private_Init_Data_Repr_0__Nat_reprFast(x_42);
lean_ctor_set_tag(x_24, 3);
lean_ctor_set(x_24, 0, x_43);
x_44 = l_Lean_MessageData_ofFormat(x_24);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_44);
lean_ctor_set(x_23, 0, x_45);
x_46 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_23);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_MessageData_ofFormat(x_40);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_1);
x_52 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_1, x_51, x_6, x_7, x_8, x_9, x_41);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_14 = x_54;
x_15 = x_53;
goto block_20;
}
else
{
uint8_t x_55; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_24, 0);
lean_inc(x_59);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_8);
x_60 = l_Lean_Compiler_LCNF_ppDecl_x27(x_59, x_8, x_9, x_35);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Compiler_LCNF_Decl_size(x_13);
lean_dec(x_13);
x_64 = l___private_Init_Data_Repr_0__Nat_reprFast(x_63);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_MessageData_ofFormat(x_65);
x_67 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_66);
lean_ctor_set(x_23, 0, x_67);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_23);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_MessageData_ofFormat(x_61);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_1);
x_74 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_1, x_73, x_6, x_7, x_8, x_9, x_62);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_14 = x_76;
x_15 = x_75;
goto block_20;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_23);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_60, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_79 = x_60;
} else {
 lean_dec_ref(x_60);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_23, 1);
lean_inc(x_81);
lean_dec(x_23);
x_82 = lean_ctor_get(x_24, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_83 = x_24;
} else {
 lean_dec_ref(x_24);
 x_83 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
x_84 = l_Lean_Compiler_LCNF_ppDecl_x27(x_82, x_8, x_9, x_81);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Compiler_LCNF_Decl_size(x_13);
lean_dec(x_13);
x_88 = l___private_Init_Data_Repr_0__Nat_reprFast(x_87);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(3, 1, 0);
} else {
 x_89 = x_83;
 lean_ctor_set_tag(x_89, 3);
}
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_MessageData_ofFormat(x_89);
x_91 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_MessageData_ofFormat(x_85);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_1);
x_99 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_1, x_98, x_6, x_7, x_8, x_9, x_86);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_14 = x_101;
x_15 = x_100;
goto block_20;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_83);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_102 = lean_ctor_get(x_84, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_84, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_104 = x_84;
} else {
 lean_dec_ref(x_84);
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
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_16;
x_10 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_shouldGenerateCode(x_11, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_array_push(x_4, x_11);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_4 = x_20;
x_9 = x_19;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_13 = lean_array_uget(x_2, x_4);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = 1;
x_23 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_21, x_22, x_8, x_9, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_panic___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__15(x_26, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_14 = x_29;
x_15 = x_28;
goto block_20;
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_23, 1);
x_36 = lean_ctor_get(x_23, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_24, 0);
lean_inc(x_9);
lean_inc(x_8);
x_39 = l_Lean_Compiler_LCNF_ppDecl_x27(x_38, x_8, x_9, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_Decl_size(x_13);
lean_dec(x_13);
x_43 = l___private_Init_Data_Repr_0__Nat_reprFast(x_42);
lean_ctor_set_tag(x_24, 3);
lean_ctor_set(x_24, 0, x_43);
x_44 = l_Lean_MessageData_ofFormat(x_24);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_44);
lean_ctor_set(x_23, 0, x_45);
x_46 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_23);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_MessageData_ofFormat(x_40);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_1);
x_52 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_1, x_51, x_6, x_7, x_8, x_9, x_41);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_14 = x_54;
x_15 = x_53;
goto block_20;
}
else
{
uint8_t x_55; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_24, 0);
lean_inc(x_59);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_8);
x_60 = l_Lean_Compiler_LCNF_ppDecl_x27(x_59, x_8, x_9, x_35);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Compiler_LCNF_Decl_size(x_13);
lean_dec(x_13);
x_64 = l___private_Init_Data_Repr_0__Nat_reprFast(x_63);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_MessageData_ofFormat(x_65);
x_67 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_66);
lean_ctor_set(x_23, 0, x_67);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_23);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_MessageData_ofFormat(x_61);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_1);
x_74 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_1, x_73, x_6, x_7, x_8, x_9, x_62);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_14 = x_76;
x_15 = x_75;
goto block_20;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_23);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_60, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_79 = x_60;
} else {
 lean_dec_ref(x_60);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_23, 1);
lean_inc(x_81);
lean_dec(x_23);
x_82 = lean_ctor_get(x_24, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_83 = x_24;
} else {
 lean_dec_ref(x_24);
 x_83 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
x_84 = l_Lean_Compiler_LCNF_ppDecl_x27(x_82, x_8, x_9, x_81);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Compiler_LCNF_Decl_size(x_13);
lean_dec(x_13);
x_88 = l___private_Init_Data_Repr_0__Nat_reprFast(x_87);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(3, 1, 0);
} else {
 x_89 = x_83;
 lean_ctor_set_tag(x_89, 3);
}
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_MessageData_ofFormat(x_89);
x_91 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_MessageData_ofFormat(x_85);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_1);
x_99 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_1, x_98, x_6, x_7, x_8, x_9, x_86);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_14 = x_101;
x_15 = x_100;
goto block_20;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_83);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_102 = lean_ctor_get(x_84, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_84, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_104 = x_84;
} else {
 lean_dec_ref(x_84);
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
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_16;
x_10 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("result", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1(x_9, x_10, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_markRecDecls(x_12);
x_15 = l_Lean_Compiler_LCNF_getPassManager___rarg(x_6, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_16);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6(x_16, x_19, x_10, x_14, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__2;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_23, x_3, x_4, x_5, x_6, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_array_get_size(x_21);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8(x_23, x_21, x_33, x_10, x_34, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_21);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_21);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1(x_9, x_10, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_markRecDecls(x_12);
x_15 = l_Lean_Compiler_LCNF_getPassManager___rarg(x_6, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_16);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6(x_16, x_19, x_10, x_14, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__2;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_23, x_3, x_4, x_5, x_6, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_array_get_size(x_21);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__10(x_23, x_21, x_33, x_10, x_34, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_21);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_21);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 4);
x_12 = lean_unsigned_to_nat(8192u);
x_13 = lean_nat_dec_le(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_ctor_set(x_4, 4, x_12);
if (x_9 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
x_22 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_14 = x_22;
x_15 = x_6;
goto block_21;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_7, x_7);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_7);
x_24 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_14 = x_24;
x_15 = x_6;
goto block_21;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_27 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_1, x_25, x_26, x_27, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_14 = x_29;
x_15 = x_30;
goto block_21;
}
else
{
uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
block_21:
{
uint8_t x_16; 
x_16 = l_Array_isEmpty___rarg(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2(x_14, x_17, x_2, x_3, x_4, x_5, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
if (x_9 == 0)
{
lean_object* x_43; 
lean_dec(x_7);
x_43 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_35 = x_43;
x_36 = x_6;
goto block_42;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_7, x_7);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_7);
x_45 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_35 = x_45;
x_36 = x_6;
goto block_42;
}
else
{
size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; 
x_46 = 0;
x_47 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_48 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
lean_inc(x_5);
lean_inc(x_4);
x_49 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_1, x_46, x_47, x_48, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_35 = x_50;
x_36 = x_51;
goto block_42;
}
else
{
uint8_t x_52; 
lean_dec(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
block_42:
{
uint8_t x_37; 
x_37 = l_Array_isEmpty___rarg(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3(x_35, x_38, x_2, x_3, x_4, x_5, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_40 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_71; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 1);
x_58 = lean_ctor_get(x_4, 2);
x_59 = lean_ctor_get(x_4, 3);
x_60 = lean_ctor_get(x_4, 4);
x_61 = lean_ctor_get(x_4, 5);
x_62 = lean_ctor_get(x_4, 6);
x_63 = lean_ctor_get(x_4, 7);
x_64 = lean_ctor_get(x_4, 8);
x_65 = lean_ctor_get(x_4, 9);
x_66 = lean_ctor_get(x_4, 10);
x_67 = lean_ctor_get_uint8(x_4, sizeof(void*)*12);
x_68 = lean_ctor_get(x_4, 11);
x_69 = lean_ctor_get_uint8(x_4, sizeof(void*)*12 + 1);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_70 = lean_unsigned_to_nat(8192u);
x_71 = lean_nat_dec_le(x_70, x_60);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_60);
x_72 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_72, 0, x_56);
lean_ctor_set(x_72, 1, x_57);
lean_ctor_set(x_72, 2, x_58);
lean_ctor_set(x_72, 3, x_59);
lean_ctor_set(x_72, 4, x_70);
lean_ctor_set(x_72, 5, x_61);
lean_ctor_set(x_72, 6, x_62);
lean_ctor_set(x_72, 7, x_63);
lean_ctor_set(x_72, 8, x_64);
lean_ctor_set(x_72, 9, x_65);
lean_ctor_set(x_72, 10, x_66);
lean_ctor_set(x_72, 11, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*12, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*12 + 1, x_69);
if (x_9 == 0)
{
lean_object* x_81; 
lean_dec(x_7);
x_81 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_73 = x_81;
x_74 = x_6;
goto block_80;
}
else
{
uint8_t x_82; 
x_82 = lean_nat_dec_le(x_7, x_7);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_7);
x_83 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_73 = x_83;
x_74 = x_6;
goto block_80;
}
else
{
size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; 
x_84 = 0;
x_85 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_86 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
lean_inc(x_5);
lean_inc(x_72);
x_87 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_1, x_84, x_85, x_86, x_2, x_3, x_72, x_5, x_6);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_73 = x_88;
x_74 = x_89;
goto block_80;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
block_80:
{
uint8_t x_75; 
x_75 = l_Array_isEmpty___rarg(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_box(0);
x_77 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2(x_73, x_76, x_2, x_3, x_72, x_5, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_78 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_94, 0, x_56);
lean_ctor_set(x_94, 1, x_57);
lean_ctor_set(x_94, 2, x_58);
lean_ctor_set(x_94, 3, x_59);
lean_ctor_set(x_94, 4, x_60);
lean_ctor_set(x_94, 5, x_61);
lean_ctor_set(x_94, 6, x_62);
lean_ctor_set(x_94, 7, x_63);
lean_ctor_set(x_94, 8, x_64);
lean_ctor_set(x_94, 9, x_65);
lean_ctor_set(x_94, 10, x_66);
lean_ctor_set(x_94, 11, x_68);
lean_ctor_set_uint8(x_94, sizeof(void*)*12, x_67);
lean_ctor_set_uint8(x_94, sizeof(void*)*12 + 1, x_69);
if (x_9 == 0)
{
lean_object* x_103; 
lean_dec(x_7);
x_103 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_95 = x_103;
x_96 = x_6;
goto block_102;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_7, x_7);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_7);
x_105 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_95 = x_105;
x_96 = x_6;
goto block_102;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_106 = 0;
x_107 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_108 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
lean_inc(x_5);
lean_inc(x_94);
x_109 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_1, x_106, x_107, x_108, x_2, x_3, x_94, x_5, x_6);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_95 = x_110;
x_96 = x_111;
goto block_102;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_94);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_114 = x_109;
} else {
 lean_dec_ref(x_109);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
block_102:
{
uint8_t x_97; 
x_97 = l_Array_isEmpty___rarg(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_box(0);
x_99 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3(x_95, x_98, x_2, x_3, x_94, x_5, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_100 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
return x_101;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; double x_19; double x_20; lean_object* x_21; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = lean_unbox_float(x_9);
lean_dec(x_9);
x_20 = lean_unbox_float(x_10);
lean_dec(x_10);
x_21 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_18, x_19, x_20, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; double x_19; double x_20; lean_object* x_21; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox_float(x_8);
lean_dec(x_8);
x_20 = lean_unbox_float(x_9);
lean_dec(x_9);
x_21 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_1, x_17, x_3, x_4, x_5, x_6, x_18, x_19, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4(x_1, x_2, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__10(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PassManager_run___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PassManager_run(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_compile___closed__1;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_compile___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_LCNF_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassManager_run___boxed), 6, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Compiler_LCNF_compile___closed__3;
x_7 = 0;
x_8 = l_Lean_Compiler_LCNF_CompilerM_run___rarg(x_5, x_6, x_7, x_2, x_3, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_showDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<not-available>", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_showDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_showDecl___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_showDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_2, x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l_Lean_Compiler_LCNF_showDecl___closed__2;
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Lean_Compiler_LCNF_showDecl___closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Lean_Compiler_LCNF_ppDecl_x27(x_15, x_3, x_4, x_14);
return x_16;
}
}
}
lean_object* l_Lean_Compiler_LCNF_showDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Compiler_LCNF_showDecl(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compiling new: ", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_main___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_1, x_6);
x_8 = l_Lean_MessageData_ofList(x_7);
x_9 = l_Lean_Compiler_LCNF_main___lambda__1___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
lean_object* l_Lean_Compiler_LCNF_main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PassManager_run(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compilation new", 15);
return x_1;
}
}
lean_object* lean_lcnf_compile_decls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_main___lambda__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_List_redLength___rarg(x_1);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec(x_7);
x_9 = l_List_toArrayAux___rarg(x_1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_main___lambda__2___boxed), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lean_Compiler_LCNF_compile___closed__3;
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CompilerM_run___rarg___boxed), 6, 3);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_13);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2;
x_16 = 1;
x_17 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_addDecl___spec__6___boxed), 8, 5);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_6);
lean_closure_set(x_19, 2, x_14);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_17);
x_20 = l_Lean_Compiler_LCNF_main___closed__1;
x_21 = lean_box(0);
x_22 = l_Lean_profileitM___at_Lean_addDecl___spec__8___rarg(x_20, x_5, x_19, x_21, x_2, x_3, x_4);
lean_dec(x_5);
return x_22;
}
}
lean_object* l_Lean_Compiler_LCNF_main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_main___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Compiler_LCNF_main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_main___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("init", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__4;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LCNF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__11;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__12;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__13;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Main", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__14;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__16;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__18;
x_2 = lean_unsigned_to_nat(1414u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("test", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__20;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("jp", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__22;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__2;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__19;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__21;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__2;
x_11 = l_Lean_registerTraceClass(x_10, x_3, x_4, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__23;
x_14 = 0;
x_15 = l_Lean_registerTraceClass(x_13, x_14, x_4, x_12);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Passes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullLetDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CSE(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___closed__1);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__15 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__15);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__16 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__16);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__17 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__17);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__18 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__18);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__19 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__19);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__20 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__20);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__21 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__21);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__22 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__22);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__23 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__23);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__24 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__24();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__24);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__25 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__25();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__25);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__26 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__26();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__26);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4);
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1();
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__2);
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__1);
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__2);
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__1);
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2);
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3);
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__4 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__4();
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5();
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__4);
l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1);
l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__2);
l_Lean_Compiler_LCNF_compile___closed__1 = _init_l_Lean_Compiler_LCNF_compile___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__1);
l_Lean_Compiler_LCNF_compile___closed__2 = _init_l_Lean_Compiler_LCNF_compile___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__2);
l_Lean_Compiler_LCNF_compile___closed__3 = _init_l_Lean_Compiler_LCNF_compile___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__3);
l_Lean_Compiler_LCNF_showDecl___closed__1 = _init_l_Lean_Compiler_LCNF_showDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_showDecl___closed__1);
l_Lean_Compiler_LCNF_showDecl___closed__2 = _init_l_Lean_Compiler_LCNF_showDecl___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_showDecl___closed__2);
l_Lean_Compiler_LCNF_main___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_main___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_main___lambda__1___closed__1);
l_Lean_Compiler_LCNF_main___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_main___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_main___lambda__1___closed__2);
l_Lean_Compiler_LCNF_main___closed__1 = _init_l_Lean_Compiler_LCNF_main___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_main___closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__17);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__18 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__18);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__19 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__19);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__20 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__20);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__21 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__21);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__22 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__22);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__23 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414____closed__23);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1414_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
