// Lean compiler output
// Module: Lean.Compiler.LCNF.Main
// Imports: Lean.Compiler.Options Lean.Compiler.ExternAttr Lean.Compiler.IR Lean.Compiler.IR.Basic Lean.Compiler.IR.Checker Lean.Compiler.IR.ToIR Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.Passes Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.ToDecl Lean.Compiler.LCNF.Check Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.CSE
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__5(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4;
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3;
lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_compile___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__23;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__4;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__7;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__19;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__13(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LogEntry_fmt(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__11;
static lean_object* l_Lean_Compiler_LCNF_compile___closed__5;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_casesOnSuffix;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_getPassManager___rarg(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_main___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_PassManager_run___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_lcnf_compile_decls(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_PassManager_run___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_compile___closed__4;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_showDecl___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__21;
lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__20;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__2;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__1(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_withPhase___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2;
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__13;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_profileitM___at_Lean_traceBlock___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__2;
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2;
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_PassManager_run___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_markRecDecls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__17;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__22;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__4(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_compile___closed__2;
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__18;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Kernel_Environment_find_x3f___spec__5(lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_check;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6;
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__8;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__16;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4;
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8;
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__12;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12;
static double l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2;
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_find_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__3;
lean_object* lean_ir_compile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_showDecl___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_trace_profiler;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__15;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_main___closed__1;
lean_object* l_List_mapTR_loop___at_Lean_compileDecls_doCompile___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_implementedByAttr;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__14(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_main___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12;
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_compile___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Compiler_LCNF_PassManager_run___spec__3___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__3;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__1;
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
extern lean_object* l_Lean_compiler_enableNew;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13;
double lean_float_sub(double, double);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_PassManager_run___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_find_x3f___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_7, x_20);
lean_dec(x_7);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Kernel_Environment_find_x3f___spec__5(x_2, x_21);
lean_dec(x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = l_Lean_Name_hash___override(x_2);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_27, x_40);
lean_dec(x_27);
x_42 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Kernel_Environment_find_x3f___spec__5(x_2, x_41);
lean_dec(x_41);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_7 = l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__2(x_1, x_4, x_5, x_6);
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
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_implementedByAttr;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_instInhabitedName;
x_8 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___closed__1;
lean_inc(x_1);
lean_inc(x_2);
x_9 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_7, x_8, x_2, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3(x_1, x_2, x_10, x_4, x_5, x_6);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; 
x_7 = 2;
lean_inc(x_1);
lean_inc(x_2);
x_8 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_2, x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4(x_1, x_2, x_9, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = l_Lean_Environment_constants(x_1);
x_8 = l_Lean_SMap_find_x3f___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1(x_7, x_2);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = 1;
x_14 = l_Lean_ConstantInfo_hasValue(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5(x_2, x_1, x_18, x_4, x_5, x_6);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_10);
x_11 = l_Lean_isExtern(x_10, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_6);
x_12 = lean_box(0);
x_13 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6(x_10, x_1, x_12, x_3, x_4, x_9);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = 1;
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
lean_inc(x_18);
x_19 = l_Lean_isExtern(x_18, x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6(x_18, x_1, x_20, x_3, x_4, x_17);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = 2;
x_6 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, 1, x_1);
lean_ctor_set_uint8(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, 5, x_2);
lean_ctor_set_uint8(x_6, 6, x_2);
lean_ctor_set_uint8(x_6, 7, x_1);
lean_ctor_set_uint8(x_6, 8, x_2);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_4);
lean_ctor_set_uint8(x_6, 11, x_2);
lean_ctor_set_uint8(x_6, 12, x_2);
lean_ctor_set_uint8(x_6, 13, x_2);
lean_ctor_set_uint8(x_6, 14, x_5);
lean_ctor_set_uint8(x_6, 15, x_2);
lean_ctor_set_uint8(x_6, 16, x_2);
lean_ctor_set_uint8(x_6, 17, x_2);
return x_6;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2;
x_5 = 0;
x_6 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8;
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_2);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set(x_9, 6, x_2);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 8, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 9, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 10, x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
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
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
x_5 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
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
x_17 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__7(x_1, x_16, x_2, x_3, x_15);
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
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isMatcher___at_Lean_Compiler_LCNF_shouldGenerateCode___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_compiler_check;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("size: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1;
x_15 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_14);
lean_ctor_set(x_8, 4, x_15);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*13, x_2);
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
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_20, x_4, x_5, x_8, x_9, x_19);
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
x_32 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_31);
lean_ctor_set(x_16, 0, x_32);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_26);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_3, x_38, x_4, x_5, x_8, x_9, x_27);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_40, x_4, x_5, x_8, x_9, x_41);
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
x_55 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_MessageData_ofFormat(x_49);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_3, x_62, x_4, x_5, x_8, x_9, x_50);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_64, x_4, x_5, x_8, x_9, x_65);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
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
x_81 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_82 = lean_ctor_get(x_8, 12);
lean_inc(x_82);
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
x_83 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1;
x_84 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_83);
x_85 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_72);
lean_ctor_set(x_85, 2, x_1);
lean_ctor_set(x_85, 3, x_73);
lean_ctor_set(x_85, 4, x_84);
lean_ctor_set(x_85, 5, x_74);
lean_ctor_set(x_85, 6, x_75);
lean_ctor_set(x_85, 7, x_76);
lean_ctor_set(x_85, 8, x_77);
lean_ctor_set(x_85, 9, x_78);
lean_ctor_set(x_85, 10, x_79);
lean_ctor_set(x_85, 11, x_80);
lean_ctor_set(x_85, 12, x_82);
lean_ctor_set_uint8(x_85, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_85, sizeof(void*)*13 + 1, x_81);
lean_inc(x_3);
x_86 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_3, x_4, x_5, x_85, x_9, x_10);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_3);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_box(0);
x_91 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_90, x_4, x_5, x_85, x_9, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_93 = x_86;
} else {
 lean_dec_ref(x_86);
 x_93 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_85);
lean_inc(x_6);
x_94 = l_Lean_Compiler_LCNF_ppDecl_x27(x_6, x_85, x_9, x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Compiler_LCNF_Decl_size(x_6);
x_98 = l___private_Init_Data_Repr_0__Nat_reprFast(x_97);
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_Lean_MessageData_ofFormat(x_99);
x_101 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
if (lean_is_scalar(x_93)) {
 x_102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_102 = x_93;
 lean_ctor_set_tag(x_102, 7);
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_MessageData_ofFormat(x_95);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_3, x_108, x_4, x_5, x_85, x_9, x_96);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_6, x_110, x_4, x_5, x_85, x_9, x_111);
lean_dec(x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_93);
lean_dec(x_85);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = lean_ctor_get(x_94, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_94, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_115 = x_94;
} else {
 lean_dec_ref(x_94);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pp", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motives", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pi", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_68; 
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2;
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6;
x_13 = 0;
x_14 = l_Lean_KVMap_setBool(x_11, x_12, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7;
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
x_68 = l_Lean_Kernel_isDiagnosticsEnabled(x_20);
lean_dec(x_20);
if (x_68 == 0)
{
if (x_16 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_box(0);
x_70 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(x_14, x_16, x_10, x_4, x_5, x_2, x_69, x_6, x_7, x_19);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
x_73 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_70);
if (x_77 == 0)
{
return x_70;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_70, 0);
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_70);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; 
x_81 = lean_box(0);
x_21 = x_81;
goto block_67;
}
}
else
{
if (x_16 == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_21 = x_82;
goto block_67;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_box(0);
x_84 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(x_14, x_16, x_10, x_4, x_5, x_2, x_83, x_6, x_7, x_19);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
x_87 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_84);
if (x_91 == 0)
{
return x_84;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_84, 0);
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_84);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
block_67:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_21);
x_22 = lean_st_ref_take(x_7, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 5);
lean_dec(x_27);
x_28 = l_Lean_Kernel_enableDiag(x_26, x_16);
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8;
lean_ctor_set(x_23, 5, x_29);
lean_ctor_set(x_23, 0, x_28);
x_30 = lean_st_ref_set(x_7, x_23, x_24);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(x_14, x_16, x_10, x_4, x_5, x_2, x_32, x_6, x_7, x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_44 = lean_ctor_get(x_23, 0);
x_45 = lean_ctor_get(x_23, 1);
x_46 = lean_ctor_get(x_23, 2);
x_47 = lean_ctor_get(x_23, 3);
x_48 = lean_ctor_get(x_23, 4);
x_49 = lean_ctor_get(x_23, 6);
x_50 = lean_ctor_get(x_23, 7);
x_51 = lean_ctor_get(x_23, 8);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_23);
x_52 = l_Lean_Kernel_enableDiag(x_44, x_16);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8;
x_54 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_46);
lean_ctor_set(x_54, 3, x_47);
lean_ctor_set(x_54, 4, x_48);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set(x_54, 6, x_49);
lean_ctor_set(x_54, 7, x_50);
lean_ctor_set(x_54, 8, x_51);
x_55 = lean_st_ref_set(x_7, x_54, x_24);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(x_14, x_16, x_10, x_4, x_5, x_2, x_57, x_6, x_7, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
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
x_61 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stat", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2;
x_17 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_16, x_8, x_9, x_10, x_11, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(x_1, x_15, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = 1;
x_33 = lean_usize_add(x_6, x_32);
x_6 = x_33;
x_7 = x_31;
x_12 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
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
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_40 = lean_ctor_get(x_17, 1);
x_41 = lean_ctor_get(x_17, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
x_43 = l_Lean_MessageData_ofName(x_42);
x_44 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_43);
lean_ctor_set(x_17, 0, x_44);
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_17);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Compiler_LCNF_Decl_size(x_15);
x_48 = l___private_Init_Data_Repr_0__Nat_reprFast(x_47);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
x_53 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_16, x_52, x_8, x_9, x_10, x_11, x_40);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_56 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(x_1, x_15, x_54, x_8, x_9, x_10, x_11, x_55);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; 
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_dec(x_56);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
lean_dec(x_57);
x_66 = 1;
x_67 = lean_usize_add(x_6, x_66);
x_6 = x_67;
x_7 = x_65;
x_12 = x_64;
goto _start;
}
}
else
{
uint8_t x_69; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_56);
if (x_69 == 0)
{
return x_56;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_56, 0);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_56);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_73 = lean_ctor_get(x_17, 1);
lean_inc(x_73);
lean_dec(x_17);
x_74 = lean_ctor_get(x_15, 0);
lean_inc(x_74);
x_75 = l_Lean_MessageData_ofName(x_74);
x_76 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Compiler_LCNF_Decl_size(x_15);
x_81 = l___private_Init_Data_Repr_0__Nat_reprFast(x_80);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_Lean_MessageData_ofFormat(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_76);
x_86 = l_Lean_addTrace___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__2(x_16, x_85, x_8, x_9, x_10, x_11, x_73);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_89 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(x_1, x_15, x_87, x_8, x_9, x_10, x_11, x_88);
lean_dec(x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; 
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
lean_dec(x_90);
x_97 = 1;
x_98 = lean_usize_add(x_6, x_97);
x_6 = x_98;
x_7 = x_96;
x_12 = x_95;
goto _start;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_100 = lean_ctor_get(x_89, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_89, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_102 = x_89;
} else {
 lean_dec_ref(x_89);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1(x_1, x_2, x_8, x_2, x_9, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
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
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1;
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
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 4);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_5);
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
x_16 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
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
x_23 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
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
x_39 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
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
x_14 = lean_ctor_get(x_12, 4);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_29);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
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
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 4);
lean_inc(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_33, 1);
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_34, 4);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_35, 0);
lean_dec(x_42);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 0, x_3);
x_43 = l_Lean_PersistentArray_push___rarg(x_1, x_33);
lean_ctor_set(x_35, 0, x_43);
x_44 = lean_st_ref_set(x_8, x_34, x_37);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint64_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get_uint64(x_35, sizeof(void*)*1);
lean_dec(x_35);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 0, x_3);
x_52 = l_Lean_PersistentArray_push___rarg(x_1, x_33);
x_53 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint64(x_53, sizeof(void*)*1, x_51);
lean_ctor_set(x_34, 4, x_53);
x_54 = lean_st_ref_set(x_8, x_34, x_37);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_59 = lean_ctor_get(x_34, 0);
x_60 = lean_ctor_get(x_34, 1);
x_61 = lean_ctor_get(x_34, 2);
x_62 = lean_ctor_get(x_34, 3);
x_63 = lean_ctor_get(x_34, 5);
x_64 = lean_ctor_get(x_34, 6);
x_65 = lean_ctor_get(x_34, 7);
x_66 = lean_ctor_get(x_34, 8);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_34);
x_67 = lean_ctor_get_uint64(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_68 = x_35;
} else {
 lean_dec_ref(x_35);
 x_68 = lean_box(0);
}
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 0, x_3);
x_69 = l_Lean_PersistentArray_push___rarg(x_1, x_33);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 1, 8);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set_uint64(x_70, sizeof(void*)*1, x_67);
x_71 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_60);
lean_ctor_set(x_71, 2, x_61);
lean_ctor_set(x_71, 3, x_62);
lean_ctor_set(x_71, 4, x_70);
lean_ctor_set(x_71, 5, x_63);
lean_ctor_set(x_71, 6, x_64);
lean_ctor_set(x_71, 7, x_65);
lean_ctor_set(x_71, 8, x_66);
x_72 = lean_st_ref_set(x_8, x_71, x_37);
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
x_75 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint64_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_77 = lean_ctor_get(x_33, 1);
lean_inc(x_77);
lean_dec(x_33);
x_78 = lean_ctor_get(x_34, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_34, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_34, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_34, 5);
lean_inc(x_82);
x_83 = lean_ctor_get(x_34, 6);
lean_inc(x_83);
x_84 = lean_ctor_get(x_34, 7);
lean_inc(x_84);
x_85 = lean_ctor_get(x_34, 8);
lean_inc(x_85);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 lean_ctor_release(x_34, 5);
 lean_ctor_release(x_34, 6);
 lean_ctor_release(x_34, 7);
 lean_ctor_release(x_34, 8);
 x_86 = x_34;
} else {
 lean_dec_ref(x_34);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get_uint64(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_88 = x_35;
} else {
 lean_dec_ref(x_35);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_3);
lean_ctor_set(x_89, 1, x_25);
x_90 = l_Lean_PersistentArray_push___rarg(x_1, x_89);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 1, 8);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set_uint64(x_91, sizeof(void*)*1, x_87);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 9, 0);
} else {
 x_92 = x_86;
}
lean_ctor_set(x_92, 0, x_78);
lean_ctor_set(x_92, 1, x_79);
lean_ctor_set(x_92, 2, x_80);
lean_ctor_set(x_92, 3, x_81);
lean_ctor_set(x_92, 4, x_91);
lean_ctor_set(x_92, 5, x_82);
lean_ctor_set(x_92, 6, x_83);
lean_ctor_set(x_92, 7, x_84);
lean_ctor_set(x_92, 8, x_85);
x_93 = lean_st_ref_set(x_8, x_92, x_77);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint64_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_98 = lean_ctor_get(x_25, 0);
x_99 = lean_ctor_get(x_25, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_25);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_100);
lean_dec(x_100);
x_102 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
lean_inc(x_10);
x_103 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_103, 0, x_24);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_101);
lean_ctor_set(x_103, 3, x_10);
x_104 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_20);
x_105 = lean_st_ref_take(x_8, x_99);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_106, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_106, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_106, 5);
lean_inc(x_114);
x_115 = lean_ctor_get(x_106, 6);
lean_inc(x_115);
x_116 = lean_ctor_get(x_106, 7);
lean_inc(x_116);
x_117 = lean_ctor_get(x_106, 8);
lean_inc(x_117);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 lean_ctor_release(x_106, 5);
 lean_ctor_release(x_106, 6);
 lean_ctor_release(x_106, 7);
 lean_ctor_release(x_106, 8);
 x_118 = x_106;
} else {
 lean_dec_ref(x_106);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get_uint64(x_107, sizeof(void*)*1);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_120 = x_107;
} else {
 lean_dec_ref(x_107);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_109;
}
lean_ctor_set(x_121, 0, x_3);
lean_ctor_set(x_121, 1, x_104);
x_122 = l_Lean_PersistentArray_push___rarg(x_1, x_121);
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(0, 1, 8);
} else {
 x_123 = x_120;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set_uint64(x_123, sizeof(void*)*1, x_119);
if (lean_is_scalar(x_118)) {
 x_124 = lean_alloc_ctor(0, 9, 0);
} else {
 x_124 = x_118;
}
lean_ctor_set(x_124, 0, x_110);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_124, 2, x_112);
lean_ctor_set(x_124, 3, x_113);
lean_ctor_set(x_124, 4, x_123);
lean_ctor_set(x_124, 5, x_114);
lean_ctor_set(x_124, 6, x_115);
lean_ctor_set(x_124, 7, x_116);
lean_ctor_set(x_124, 8, x_117);
x_125 = lean_st_ref_set(x_8, x_124, x_108);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = lean_box(0);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (x_7 == 0)
{
double x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_17 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set_float(x_17, sizeof(void*)*2, x_16);
lean_ctor_set_float(x_17, sizeof(void*)*2 + 8, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 16, x_2);
x_18 = lean_box(0);
x_19 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1(x_4, x_5, x_10, x_6, x_17, x_18, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_8);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_9);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_2);
x_21 = lean_box(0);
x_22 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__1(x_4, x_5, x_10, x_6, x_20, x_21, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, double x_7, double x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 5);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_17 = lean_apply_6(x_9, x_5, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_18, x_11, x_12, x_13, x_14, x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__2;
x_23 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_22, x_11, x_12, x_13, x_14, x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
return x_23;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHeartbeats;
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
lean_object* x_19; lean_object* x_20; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_io_mono_nanos_now(x_16);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_117 = lean_apply_5(x_7, x_9, x_10, x_11, x_12, x_116);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_119);
x_122 = lean_io_mono_nanos_now(x_120);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; double x_128; double x_129; double x_130; double x_131; double x_132; lean_object* x_133; lean_object* x_134; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get(x_122, 1);
x_126 = 0;
x_127 = lean_unsigned_to_nat(0u);
x_128 = l_Float_ofScientific(x_115, x_126, x_127);
lean_dec(x_115);
x_129 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_130 = lean_float_div(x_128, x_129);
x_131 = l_Float_ofScientific(x_124, x_126, x_127);
lean_dec(x_124);
x_132 = lean_float_div(x_131, x_129);
x_133 = lean_box_float(x_130);
x_134 = lean_box_float(x_132);
lean_ctor_set(x_122, 1, x_134);
lean_ctor_set(x_122, 0, x_133);
lean_ctor_set(x_117, 1, x_122);
lean_ctor_set(x_117, 0, x_121);
x_19 = x_117;
x_20 = x_125;
goto block_113;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; double x_139; double x_140; double x_141; double x_142; double x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_135 = lean_ctor_get(x_122, 0);
x_136 = lean_ctor_get(x_122, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_122);
x_137 = 0;
x_138 = lean_unsigned_to_nat(0u);
x_139 = l_Float_ofScientific(x_115, x_137, x_138);
lean_dec(x_115);
x_140 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_141 = lean_float_div(x_139, x_140);
x_142 = l_Float_ofScientific(x_135, x_137, x_138);
lean_dec(x_135);
x_143 = lean_float_div(x_142, x_140);
x_144 = lean_box_float(x_141);
x_145 = lean_box_float(x_143);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_117, 1, x_146);
lean_ctor_set(x_117, 0, x_121);
x_19 = x_117;
x_20 = x_136;
goto block_113;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; double x_156; double x_157; double x_158; double x_159; double x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_147 = lean_ctor_get(x_117, 0);
x_148 = lean_ctor_get(x_117, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_117);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_147);
x_150 = lean_io_mono_nanos_now(x_148);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = 0;
x_155 = lean_unsigned_to_nat(0u);
x_156 = l_Float_ofScientific(x_115, x_154, x_155);
lean_dec(x_115);
x_157 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_158 = lean_float_div(x_156, x_157);
x_159 = l_Float_ofScientific(x_151, x_154, x_155);
lean_dec(x_151);
x_160 = lean_float_div(x_159, x_157);
x_161 = lean_box_float(x_158);
x_162 = lean_box_float(x_160);
if (lean_is_scalar(x_153)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_153;
}
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_149);
lean_ctor_set(x_164, 1, x_163);
x_19 = x_164;
x_20 = x_152;
goto block_113;
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_117);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_117, 0);
x_167 = lean_ctor_get(x_117, 1);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_166);
x_169 = lean_io_mono_nanos_now(x_167);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; double x_175; double x_176; double x_177; double x_178; double x_179; lean_object* x_180; lean_object* x_181; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_ctor_get(x_169, 1);
x_173 = 0;
x_174 = lean_unsigned_to_nat(0u);
x_175 = l_Float_ofScientific(x_115, x_173, x_174);
lean_dec(x_115);
x_176 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_177 = lean_float_div(x_175, x_176);
x_178 = l_Float_ofScientific(x_171, x_173, x_174);
lean_dec(x_171);
x_179 = lean_float_div(x_178, x_176);
x_180 = lean_box_float(x_177);
x_181 = lean_box_float(x_179);
lean_ctor_set(x_169, 1, x_181);
lean_ctor_set(x_169, 0, x_180);
lean_ctor_set_tag(x_117, 0);
lean_ctor_set(x_117, 1, x_169);
lean_ctor_set(x_117, 0, x_168);
x_19 = x_117;
x_20 = x_172;
goto block_113;
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; double x_186; double x_187; double x_188; double x_189; double x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_182 = lean_ctor_get(x_169, 0);
x_183 = lean_ctor_get(x_169, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_169);
x_184 = 0;
x_185 = lean_unsigned_to_nat(0u);
x_186 = l_Float_ofScientific(x_115, x_184, x_185);
lean_dec(x_115);
x_187 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_188 = lean_float_div(x_186, x_187);
x_189 = l_Float_ofScientific(x_182, x_184, x_185);
lean_dec(x_182);
x_190 = lean_float_div(x_189, x_187);
x_191 = lean_box_float(x_188);
x_192 = lean_box_float(x_190);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set_tag(x_117, 0);
lean_ctor_set(x_117, 1, x_193);
lean_ctor_set(x_117, 0, x_168);
x_19 = x_117;
x_20 = x_183;
goto block_113;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; double x_203; double x_204; double x_205; double x_206; double x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_194 = lean_ctor_get(x_117, 0);
x_195 = lean_ctor_get(x_117, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_117);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_194);
x_197 = lean_io_mono_nanos_now(x_195);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
x_201 = 0;
x_202 = lean_unsigned_to_nat(0u);
x_203 = l_Float_ofScientific(x_115, x_201, x_202);
lean_dec(x_115);
x_204 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_205 = lean_float_div(x_203, x_204);
x_206 = l_Float_ofScientific(x_198, x_201, x_202);
lean_dec(x_198);
x_207 = lean_float_div(x_206, x_204);
x_208 = lean_box_float(x_205);
x_209 = lean_box_float(x_207);
if (lean_is_scalar(x_200)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_200;
}
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_196);
lean_ctor_set(x_211, 1, x_210);
x_19 = x_211;
x_20 = x_199;
goto block_113;
}
}
block_113:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
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
x_25 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
x_26 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_1, x_25);
if (x_26 == 0)
{
if (x_6 == 0)
{
uint8_t x_93; 
x_93 = 0;
x_27 = x_93;
goto block_92;
}
else
{
lean_object* x_94; double x_95; double x_96; lean_object* x_97; 
x_94 = lean_box(0);
x_95 = lean_unbox_float(x_23);
lean_dec(x_23);
x_96 = lean_unbox_float(x_24);
lean_dec(x_24);
x_97 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_22, x_26, x_95, x_96, x_5, x_94, x_9, x_10, x_11, x_12, x_20);
return x_97;
}
}
else
{
if (x_6 == 0)
{
double x_98; double x_99; double x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; double x_105; double x_106; double x_107; uint8_t x_108; 
x_98 = lean_unbox_float(x_24);
x_99 = lean_unbox_float(x_23);
x_100 = lean_float_sub(x_98, x_99);
x_101 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3;
x_102 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_101);
x_103 = 0;
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Float_ofScientific(x_102, x_103, x_104);
lean_dec(x_102);
x_106 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__4;
x_107 = lean_float_div(x_105, x_106);
x_108 = lean_float_decLt(x_107, x_100);
x_27 = x_108;
goto block_92;
}
else
{
lean_object* x_109; double x_110; double x_111; lean_object* x_112; 
x_109 = lean_box(0);
x_110 = lean_unbox_float(x_23);
lean_dec(x_23);
x_111 = lean_unbox_float(x_24);
lean_dec(x_24);
x_112 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_22, x_26, x_110, x_111, x_5, x_109, x_9, x_10, x_11, x_12, x_20);
return x_112;
}
}
block_92:
{
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = lean_st_ref_take(x_12, x_20);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 4);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = l_Lean_PersistentArray_append___rarg(x_15, x_35);
lean_dec(x_35);
lean_ctor_set(x_30, 0, x_36);
x_37 = lean_st_ref_set(x_12, x_29, x_31);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_22, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_22);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get_uint64(x_30, sizeof(void*)*1);
x_49 = lean_ctor_get(x_30, 0);
lean_inc(x_49);
lean_dec(x_30);
x_50 = l_Lean_PersistentArray_append___rarg(x_15, x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint64(x_51, sizeof(void*)*1, x_48);
lean_ctor_set(x_29, 4, x_51);
x_52 = lean_st_ref_set(x_12, x_29, x_31);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get(x_29, 0);
x_64 = lean_ctor_get(x_29, 1);
x_65 = lean_ctor_get(x_29, 2);
x_66 = lean_ctor_get(x_29, 3);
x_67 = lean_ctor_get(x_29, 5);
x_68 = lean_ctor_get(x_29, 6);
x_69 = lean_ctor_get(x_29, 7);
x_70 = lean_ctor_get(x_29, 8);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_29);
x_71 = lean_ctor_get_uint64(x_30, sizeof(void*)*1);
x_72 = lean_ctor_get(x_30, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_73 = x_30;
} else {
 lean_dec_ref(x_30);
 x_73 = lean_box(0);
}
x_74 = l_Lean_PersistentArray_append___rarg(x_15, x_72);
lean_dec(x_72);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 1, 8);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set_uint64(x_75, sizeof(void*)*1, x_71);
x_76 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_76, 0, x_63);
lean_ctor_set(x_76, 1, x_64);
lean_ctor_set(x_76, 2, x_65);
lean_ctor_set(x_76, 3, x_66);
lean_ctor_set(x_76, 4, x_75);
lean_ctor_set(x_76, 5, x_67);
lean_ctor_set(x_76, 6, x_68);
lean_ctor_set(x_76, 7, x_69);
lean_ctor_set(x_76, 8, x_70);
x_77 = lean_st_ref_set(x_12, x_76, x_31);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_22, x_9, x_10, x_11, x_12, x_78);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_22);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
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
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_86 = x_79;
} else {
 lean_dec_ref(x_79);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
lean_object* x_88; double x_89; double x_90; lean_object* x_91; 
x_88 = lean_box(0);
x_89 = lean_unbox_float(x_23);
lean_dec(x_23);
x_90 = lean_unbox_float(x_24);
lean_dec(x_24);
x_91 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_22, x_26, x_89, x_90, x_5, x_88, x_9, x_10, x_11, x_12, x_20);
return x_91;
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_io_get_num_heartbeats(x_16);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_308 = lean_apply_5(x_7, x_9, x_10, x_11, x_12, x_307);
if (lean_obj_tag(x_308) == 0)
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = lean_ctor_get(x_308, 1);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_310);
x_313 = lean_io_get_num_heartbeats(x_311);
x_314 = !lean_is_exclusive(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; double x_319; double x_320; lean_object* x_321; lean_object* x_322; 
x_315 = lean_ctor_get(x_313, 0);
x_316 = lean_ctor_get(x_313, 1);
x_317 = 0;
x_318 = lean_unsigned_to_nat(0u);
x_319 = l_Float_ofScientific(x_306, x_317, x_318);
lean_dec(x_306);
x_320 = l_Float_ofScientific(x_315, x_317, x_318);
lean_dec(x_315);
x_321 = lean_box_float(x_319);
x_322 = lean_box_float(x_320);
lean_ctor_set(x_313, 1, x_322);
lean_ctor_set(x_313, 0, x_321);
lean_ctor_set(x_308, 1, x_313);
lean_ctor_set(x_308, 0, x_312);
x_212 = x_308;
x_213 = x_316;
goto block_304;
}
else
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; double x_327; double x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_323 = lean_ctor_get(x_313, 0);
x_324 = lean_ctor_get(x_313, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_313);
x_325 = 0;
x_326 = lean_unsigned_to_nat(0u);
x_327 = l_Float_ofScientific(x_306, x_325, x_326);
lean_dec(x_306);
x_328 = l_Float_ofScientific(x_323, x_325, x_326);
lean_dec(x_323);
x_329 = lean_box_float(x_327);
x_330 = lean_box_float(x_328);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
lean_ctor_set(x_308, 1, x_331);
lean_ctor_set(x_308, 0, x_312);
x_212 = x_308;
x_213 = x_324;
goto block_304;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; double x_341; double x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_332 = lean_ctor_get(x_308, 0);
x_333 = lean_ctor_get(x_308, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_308);
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_332);
x_335 = lean_io_get_num_heartbeats(x_333);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
x_339 = 0;
x_340 = lean_unsigned_to_nat(0u);
x_341 = l_Float_ofScientific(x_306, x_339, x_340);
lean_dec(x_306);
x_342 = l_Float_ofScientific(x_336, x_339, x_340);
lean_dec(x_336);
x_343 = lean_box_float(x_341);
x_344 = lean_box_float(x_342);
if (lean_is_scalar(x_338)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_338;
}
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_334);
lean_ctor_set(x_346, 1, x_345);
x_212 = x_346;
x_213 = x_337;
goto block_304;
}
}
else
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_308);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_348 = lean_ctor_get(x_308, 0);
x_349 = lean_ctor_get(x_308, 1);
x_350 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_350, 0, x_348);
x_351 = lean_io_get_num_heartbeats(x_349);
x_352 = !lean_is_exclusive(x_351);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; double x_357; double x_358; lean_object* x_359; lean_object* x_360; 
x_353 = lean_ctor_get(x_351, 0);
x_354 = lean_ctor_get(x_351, 1);
x_355 = 0;
x_356 = lean_unsigned_to_nat(0u);
x_357 = l_Float_ofScientific(x_306, x_355, x_356);
lean_dec(x_306);
x_358 = l_Float_ofScientific(x_353, x_355, x_356);
lean_dec(x_353);
x_359 = lean_box_float(x_357);
x_360 = lean_box_float(x_358);
lean_ctor_set(x_351, 1, x_360);
lean_ctor_set(x_351, 0, x_359);
lean_ctor_set_tag(x_308, 0);
lean_ctor_set(x_308, 1, x_351);
lean_ctor_set(x_308, 0, x_350);
x_212 = x_308;
x_213 = x_354;
goto block_304;
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; double x_365; double x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_361 = lean_ctor_get(x_351, 0);
x_362 = lean_ctor_get(x_351, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_351);
x_363 = 0;
x_364 = lean_unsigned_to_nat(0u);
x_365 = l_Float_ofScientific(x_306, x_363, x_364);
lean_dec(x_306);
x_366 = l_Float_ofScientific(x_361, x_363, x_364);
lean_dec(x_361);
x_367 = lean_box_float(x_365);
x_368 = lean_box_float(x_366);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set_tag(x_308, 0);
lean_ctor_set(x_308, 1, x_369);
lean_ctor_set(x_308, 0, x_350);
x_212 = x_308;
x_213 = x_362;
goto block_304;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; double x_379; double x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_370 = lean_ctor_get(x_308, 0);
x_371 = lean_ctor_get(x_308, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_308);
x_372 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_372, 0, x_370);
x_373 = lean_io_get_num_heartbeats(x_371);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
x_377 = 0;
x_378 = lean_unsigned_to_nat(0u);
x_379 = l_Float_ofScientific(x_306, x_377, x_378);
lean_dec(x_306);
x_380 = l_Float_ofScientific(x_374, x_377, x_378);
lean_dec(x_374);
x_381 = lean_box_float(x_379);
x_382 = lean_box_float(x_380);
if (lean_is_scalar(x_376)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_376;
}
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_372);
lean_ctor_set(x_384, 1, x_383);
x_212 = x_384;
x_213 = x_375;
goto block_304;
}
}
block_304:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_220; 
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
lean_dec(x_212);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
lean_dec(x_214);
x_218 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
x_219 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_1, x_218);
if (x_219 == 0)
{
if (x_6 == 0)
{
uint8_t x_286; 
x_286 = 0;
x_220 = x_286;
goto block_285;
}
else
{
lean_object* x_287; double x_288; double x_289; lean_object* x_290; 
x_287 = lean_box(0);
x_288 = lean_unbox_float(x_216);
lean_dec(x_216);
x_289 = lean_unbox_float(x_217);
lean_dec(x_217);
x_290 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_215, x_219, x_288, x_289, x_5, x_287, x_9, x_10, x_11, x_12, x_213);
return x_290;
}
}
else
{
if (x_6 == 0)
{
double x_291; double x_292; double x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; double x_298; uint8_t x_299; 
x_291 = lean_unbox_float(x_217);
x_292 = lean_unbox_float(x_216);
x_293 = lean_float_sub(x_291, x_292);
x_294 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3;
x_295 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_294);
x_296 = 0;
x_297 = lean_unsigned_to_nat(0u);
x_298 = l_Float_ofScientific(x_295, x_296, x_297);
lean_dec(x_295);
x_299 = lean_float_decLt(x_298, x_293);
x_220 = x_299;
goto block_285;
}
else
{
lean_object* x_300; double x_301; double x_302; lean_object* x_303; 
x_300 = lean_box(0);
x_301 = lean_unbox_float(x_216);
lean_dec(x_216);
x_302 = lean_unbox_float(x_217);
lean_dec(x_217);
x_303 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_215, x_219, x_301, x_302, x_5, x_300, x_9, x_10, x_11, x_12, x_213);
return x_303;
}
}
block_285:
{
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_221 = lean_st_ref_take(x_12, x_213);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_222, 4);
lean_inc(x_223);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_225 = !lean_is_exclusive(x_222);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_222, 4);
lean_dec(x_226);
x_227 = !lean_is_exclusive(x_223);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_223, 0);
x_229 = l_Lean_PersistentArray_append___rarg(x_15, x_228);
lean_dec(x_228);
lean_ctor_set(x_223, 0, x_229);
x_230 = lean_st_ref_set(x_12, x_222, x_224);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_215, x_9, x_10, x_11, x_12, x_231);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_215);
if (lean_obj_tag(x_232) == 0)
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
return x_232;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_232, 0);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_232);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
else
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_232);
if (x_237 == 0)
{
return x_232;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_232, 0);
x_239 = lean_ctor_get(x_232, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_232);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
uint64_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_241 = lean_ctor_get_uint64(x_223, sizeof(void*)*1);
x_242 = lean_ctor_get(x_223, 0);
lean_inc(x_242);
lean_dec(x_223);
x_243 = l_Lean_PersistentArray_append___rarg(x_15, x_242);
lean_dec(x_242);
x_244 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set_uint64(x_244, sizeof(void*)*1, x_241);
lean_ctor_set(x_222, 4, x_244);
x_245 = lean_st_ref_set(x_12, x_222, x_224);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_247 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_215, x_9, x_10, x_11, x_12, x_246);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_215);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_247, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_247, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_254 = x_247;
} else {
 lean_dec_ref(x_247);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint64_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_256 = lean_ctor_get(x_222, 0);
x_257 = lean_ctor_get(x_222, 1);
x_258 = lean_ctor_get(x_222, 2);
x_259 = lean_ctor_get(x_222, 3);
x_260 = lean_ctor_get(x_222, 5);
x_261 = lean_ctor_get(x_222, 6);
x_262 = lean_ctor_get(x_222, 7);
x_263 = lean_ctor_get(x_222, 8);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_222);
x_264 = lean_ctor_get_uint64(x_223, sizeof(void*)*1);
x_265 = lean_ctor_get(x_223, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_266 = x_223;
} else {
 lean_dec_ref(x_223);
 x_266 = lean_box(0);
}
x_267 = l_Lean_PersistentArray_append___rarg(x_15, x_265);
lean_dec(x_265);
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(0, 1, 8);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set_uint64(x_268, sizeof(void*)*1, x_264);
x_269 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_269, 0, x_256);
lean_ctor_set(x_269, 1, x_257);
lean_ctor_set(x_269, 2, x_258);
lean_ctor_set(x_269, 3, x_259);
lean_ctor_set(x_269, 4, x_268);
lean_ctor_set(x_269, 5, x_260);
lean_ctor_set(x_269, 6, x_261);
lean_ctor_set(x_269, 7, x_262);
lean_ctor_set(x_269, 8, x_263);
x_270 = lean_st_ref_set(x_12, x_269, x_224);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
x_272 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_PassManager_run___spec__5(x_215, x_9, x_10, x_11, x_12, x_271);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_215);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = lean_ctor_get(x_272, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_272, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_279 = x_272;
} else {
 lean_dec_ref(x_272);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
}
else
{
lean_object* x_281; double x_282; double x_283; lean_object* x_284; 
x_281 = lean_box(0);
x_282 = lean_unbox_float(x_216);
lean_dec(x_216);
x_283 = lean_unbox_float(x_217);
lean_dec(x_217);
x_284 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_215, x_219, x_282, x_283, x_5, x_281, x_9, x_10, x_11, x_12, x_213);
return x_284;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("new compiler phase: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", pass: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("base", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mono", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("impure", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
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
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
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
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___boxed), 7, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_apply_1(x_17, x_6);
x_19 = lean_box(x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withPhase___rarg___boxed), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2;
x_22 = 1;
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2(x_21, x_15, x_20, x_22, x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_31 = l_Lean_Compiler_LCNF_checkpoint(x_28, x_25, x_30, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; size_t x_33; size_t x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = 1;
x_34 = lean_usize_add(x_5, x_33);
x_5 = x_34;
x_6 = x_25;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
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
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 4);
lean_inc(x_24);
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
x_29 = lean_ctor_get(x_23, 4);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; double x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_33 = 0;
x_34 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_35 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_float(x_35, sizeof(void*)*2, x_32);
lean_ctor_set_float(x_35, sizeof(void*)*2 + 8, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 16, x_33);
x_36 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_37 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_13);
lean_ctor_set(x_37, 2, x_36);
lean_inc(x_8);
lean_ctor_set(x_22, 1, x_37);
lean_ctor_set(x_22, 0, x_8);
x_38 = l_Lean_PersistentArray_push___rarg(x_31, x_22);
lean_ctor_set(x_24, 0, x_38);
x_39 = lean_st_ref_set(x_6, x_23, x_26);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint64_t x_46; lean_object* x_47; double x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_46 = lean_ctor_get_uint64(x_24, sizeof(void*)*1);
x_47 = lean_ctor_get(x_24, 0);
lean_inc(x_47);
lean_dec(x_24);
x_48 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_49 = 0;
x_50 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_51 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_float(x_51, sizeof(void*)*2, x_48);
lean_ctor_set_float(x_51, sizeof(void*)*2 + 8, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 16, x_49);
x_52 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_53 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_13);
lean_ctor_set(x_53, 2, x_52);
lean_inc(x_8);
lean_ctor_set(x_22, 1, x_53);
lean_ctor_set(x_22, 0, x_8);
x_54 = l_Lean_PersistentArray_push___rarg(x_47, x_22);
x_55 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint64(x_55, sizeof(void*)*1, x_46);
lean_ctor_set(x_23, 4, x_55);
x_56 = lean_st_ref_set(x_6, x_23, x_26);
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; double x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_61 = lean_ctor_get(x_23, 0);
x_62 = lean_ctor_get(x_23, 1);
x_63 = lean_ctor_get(x_23, 2);
x_64 = lean_ctor_get(x_23, 3);
x_65 = lean_ctor_get(x_23, 5);
x_66 = lean_ctor_get(x_23, 6);
x_67 = lean_ctor_get(x_23, 7);
x_68 = lean_ctor_get(x_23, 8);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_23);
x_69 = lean_ctor_get_uint64(x_24, sizeof(void*)*1);
x_70 = lean_ctor_get(x_24, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_71 = x_24;
} else {
 lean_dec_ref(x_24);
 x_71 = lean_box(0);
}
x_72 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_73 = 0;
x_74 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_75 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set_float(x_75, sizeof(void*)*2, x_72);
lean_ctor_set_float(x_75, sizeof(void*)*2 + 8, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*2 + 16, x_73);
x_76 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_77 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_13);
lean_ctor_set(x_77, 2, x_76);
lean_inc(x_8);
lean_ctor_set(x_22, 1, x_77);
lean_ctor_set(x_22, 0, x_8);
x_78 = l_Lean_PersistentArray_push___rarg(x_70, x_22);
if (lean_is_scalar(x_71)) {
 x_79 = lean_alloc_ctor(0, 1, 8);
} else {
 x_79 = x_71;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_uint64(x_79, sizeof(void*)*1, x_69);
x_80 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_62);
lean_ctor_set(x_80, 2, x_63);
lean_ctor_set(x_80, 3, x_64);
lean_ctor_set(x_80, 4, x_79);
lean_ctor_set(x_80, 5, x_65);
lean_ctor_set(x_80, 6, x_66);
lean_ctor_set(x_80, 7, x_67);
lean_ctor_set(x_80, 8, x_68);
x_81 = lean_st_ref_set(x_6, x_80, x_26);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
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
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint64_t x_96; lean_object* x_97; lean_object* x_98; double x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_86 = lean_ctor_get(x_22, 1);
lean_inc(x_86);
lean_dec(x_22);
x_87 = lean_ctor_get(x_23, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_23, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_23, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_23, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_23, 5);
lean_inc(x_91);
x_92 = lean_ctor_get(x_23, 6);
lean_inc(x_92);
x_93 = lean_ctor_get(x_23, 7);
lean_inc(x_93);
x_94 = lean_ctor_get(x_23, 8);
lean_inc(x_94);
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
 x_95 = x_23;
} else {
 lean_dec_ref(x_23);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get_uint64(x_24, sizeof(void*)*1);
x_97 = lean_ctor_get(x_24, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_98 = x_24;
} else {
 lean_dec_ref(x_24);
 x_98 = lean_box(0);
}
x_99 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_100 = 0;
x_101 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_102 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_float(x_102, sizeof(void*)*2, x_99);
lean_ctor_set_float(x_102, sizeof(void*)*2 + 8, x_99);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 16, x_100);
x_103 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_104 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_13);
lean_ctor_set(x_104, 2, x_103);
lean_inc(x_8);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_8);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_PersistentArray_push___rarg(x_97, x_105);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(0, 1, 8);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set_uint64(x_107, sizeof(void*)*1, x_96);
if (lean_is_scalar(x_95)) {
 x_108 = lean_alloc_ctor(0, 9, 0);
} else {
 x_108 = x_95;
}
lean_ctor_set(x_108, 0, x_87);
lean_ctor_set(x_108, 1, x_88);
lean_ctor_set(x_108, 2, x_89);
lean_ctor_set(x_108, 3, x_90);
lean_ctor_set(x_108, 4, x_107);
lean_ctor_set(x_108, 5, x_91);
lean_ctor_set(x_108, 6, x_92);
lean_ctor_set(x_108, 7, x_93);
lean_ctor_set(x_108, 8, x_94);
x_109 = lean_st_ref_set(x_6, x_108, x_86);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint64_t x_136; lean_object* x_137; lean_object* x_138; double x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_114 = lean_ctor_get(x_13, 0);
x_115 = lean_ctor_get(x_13, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_13);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_116);
lean_dec(x_116);
x_118 = lean_ctor_get(x_5, 2);
x_119 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
lean_inc(x_118);
x_120 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_120, 0, x_12);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_117);
lean_ctor_set(x_120, 3, x_118);
x_121 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_2);
x_122 = lean_st_ref_take(x_6, x_115);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_123, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 5);
lean_inc(x_131);
x_132 = lean_ctor_get(x_123, 6);
lean_inc(x_132);
x_133 = lean_ctor_get(x_123, 7);
lean_inc(x_133);
x_134 = lean_ctor_get(x_123, 8);
lean_inc(x_134);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 lean_ctor_release(x_123, 6);
 lean_ctor_release(x_123, 7);
 lean_ctor_release(x_123, 8);
 x_135 = x_123;
} else {
 lean_dec_ref(x_123);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get_uint64(x_124, sizeof(void*)*1);
x_137 = lean_ctor_get(x_124, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_138 = x_124;
} else {
 lean_dec_ref(x_124);
 x_138 = lean_box(0);
}
x_139 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_140 = 0;
x_141 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_142 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_142, 0, x_1);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_float(x_142, sizeof(void*)*2, x_139);
lean_ctor_set_float(x_142, sizeof(void*)*2 + 8, x_139);
lean_ctor_set_uint8(x_142, sizeof(void*)*2 + 16, x_140);
x_143 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_144 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_121);
lean_ctor_set(x_144, 2, x_143);
lean_inc(x_8);
if (lean_is_scalar(x_126)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_126;
}
lean_ctor_set(x_145, 0, x_8);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_PersistentArray_push___rarg(x_137, x_145);
if (lean_is_scalar(x_138)) {
 x_147 = lean_alloc_ctor(0, 1, 8);
} else {
 x_147 = x_138;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set_uint64(x_147, sizeof(void*)*1, x_136);
if (lean_is_scalar(x_135)) {
 x_148 = lean_alloc_ctor(0, 9, 0);
} else {
 x_148 = x_135;
}
lean_ctor_set(x_148, 0, x_127);
lean_ctor_set(x_148, 1, x_128);
lean_ctor_set(x_148, 2, x_129);
lean_ctor_set(x_148, 3, x_130);
lean_ctor_set(x_148, 4, x_147);
lean_ctor_set(x_148, 5, x_131);
lean_ctor_set(x_148, 6, x_132);
lean_ctor_set(x_148, 7, x_133);
lean_ctor_set(x_148, 8, x_134);
x_149 = lean_st_ref_set(x_6, x_148, x_125);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = lean_box(0);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_150);
return x_153;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IR", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = l_Lean_IR_LogEntry_fmt(x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2;
x_21 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_20, x_19, x_7, x_8, x_9, x_10, x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_25 = lean_box(0);
x_5 = x_24;
x_6 = x_25;
x_11 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_PassManager_run___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_4, 2);
x_19 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_20);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_28);
lean_inc(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_3, x_32);
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
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_4, 2);
x_41 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
lean_inc(x_40);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set(x_42, 3, x_40);
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_1);
lean_inc(x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_37)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_37;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_PassManager_run___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 5);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8;
lean_ctor_set(x_8, 5, x_13);
lean_ctor_set(x_8, 0, x_1);
x_14 = lean_st_ref_set(x_5, x_8, x_9);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get(x_8, 6);
x_26 = lean_ctor_get(x_8, 7);
x_27 = lean_ctor_get(x_8, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8;
x_29 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_29, 6, x_25);
lean_ctor_set(x_29, 7, x_26);
lean_ctor_set(x_29, 8, x_27);
x_30 = lean_st_ref_set(x_5, x_29, x_9);
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Main", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.PassManager.run", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__2;
x_3 = lean_unsigned_to_nat(90u);
x_4 = lean_unsigned_to_nat(52u);
x_5 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = 1;
x_25 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_23, x_24, x_10, x_11, x_12);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = l_panic___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__7(x_28, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_16 = x_31;
x_17 = x_30;
goto block_22;
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_25, 1);
x_38 = lean_ctor_get(x_25, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_26, 0);
lean_inc(x_11);
lean_inc(x_10);
x_41 = l_Lean_Compiler_LCNF_ppDecl_x27(x_40, x_10, x_11, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Compiler_LCNF_Decl_size(x_15);
lean_dec(x_15);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_44);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 0, x_45);
x_46 = l_Lean_MessageData_ofFormat(x_26);
x_47 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_46);
lean_ctor_set(x_25, 0, x_47);
x_48 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_42);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_2);
x_54 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_2, x_53, x_8, x_9, x_10, x_11, x_43);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_16 = x_56;
x_17 = x_55;
goto block_22;
}
else
{
uint8_t x_57; 
lean_free_object(x_26);
lean_free_object(x_25);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_41);
if (x_57 == 0)
{
return x_41;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_41, 0);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_41);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_26, 0);
lean_inc(x_61);
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
x_62 = l_Lean_Compiler_LCNF_ppDecl_x27(x_61, x_10, x_11, x_37);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Compiler_LCNF_Decl_size(x_15);
lean_dec(x_15);
x_66 = l___private_Init_Data_Repr_0__Nat_reprFast(x_65);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_MessageData_ofFormat(x_67);
x_69 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_68);
lean_ctor_set(x_25, 0, x_69);
x_70 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_MessageData_ofFormat(x_63);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_2);
x_76 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_2, x_75, x_8, x_9, x_10, x_11, x_64);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_16 = x_78;
x_17 = x_77;
goto block_22;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_25);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_79 = lean_ctor_get(x_62, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_62, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_81 = x_62;
} else {
 lean_dec_ref(x_62);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_25, 1);
lean_inc(x_83);
lean_dec(x_25);
x_84 = lean_ctor_get(x_26, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_85 = x_26;
} else {
 lean_dec_ref(x_26);
 x_85 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
x_86 = l_Lean_Compiler_LCNF_ppDecl_x27(x_84, x_10, x_11, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Compiler_LCNF_Decl_size(x_15);
lean_dec(x_15);
x_90 = l___private_Init_Data_Repr_0__Nat_reprFast(x_89);
if (lean_is_scalar(x_85)) {
 x_91 = lean_alloc_ctor(3, 1, 0);
} else {
 x_91 = x_85;
 lean_ctor_set_tag(x_91, 3);
}
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_MessageData_ofFormat(x_91);
x_93 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_MessageData_ofFormat(x_87);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_2);
x_101 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_2, x_100, x_8, x_9, x_10, x_11, x_88);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_16 = x_103;
x_17 = x_102;
goto block_22;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_85);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_104 = lean_ctor_get(x_86, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_86, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_106 = x_86;
} else {
 lean_dec_ref(x_86);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_18;
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___boxed), 7, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_apply_1(x_17, x_6);
x_19 = lean_box(x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withPhase___rarg___boxed), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2;
x_22 = 1;
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2(x_21, x_15, x_20, x_22, x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_31 = l_Lean_Compiler_LCNF_checkpoint(x_28, x_25, x_30, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; size_t x_33; size_t x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = 1;
x_34 = lean_usize_add(x_5, x_33);
x_5 = x_34;
x_6 = x_25;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = l_Lean_IR_LogEntry_fmt(x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2;
x_21 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_20, x_19, x_7, x_8, x_9, x_10, x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_25 = lean_box(0);
x_5 = x_24;
x_6 = x_25;
x_11 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = 1;
x_25 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_23, x_24, x_10, x_11, x_12);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = l_panic___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__7(x_28, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_16 = x_31;
x_17 = x_30;
goto block_22;
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_25, 1);
x_38 = lean_ctor_get(x_25, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_26, 0);
lean_inc(x_11);
lean_inc(x_10);
x_41 = l_Lean_Compiler_LCNF_ppDecl_x27(x_40, x_10, x_11, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Compiler_LCNF_Decl_size(x_15);
lean_dec(x_15);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_44);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 0, x_45);
x_46 = l_Lean_MessageData_ofFormat(x_26);
x_47 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_46);
lean_ctor_set(x_25, 0, x_47);
x_48 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_42);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_2);
x_54 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_2, x_53, x_8, x_9, x_10, x_11, x_43);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_16 = x_56;
x_17 = x_55;
goto block_22;
}
else
{
uint8_t x_57; 
lean_free_object(x_26);
lean_free_object(x_25);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_41);
if (x_57 == 0)
{
return x_41;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_41, 0);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_41);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_26, 0);
lean_inc(x_61);
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
x_62 = l_Lean_Compiler_LCNF_ppDecl_x27(x_61, x_10, x_11, x_37);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Compiler_LCNF_Decl_size(x_15);
lean_dec(x_15);
x_66 = l___private_Init_Data_Repr_0__Nat_reprFast(x_65);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_MessageData_ofFormat(x_67);
x_69 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_68);
lean_ctor_set(x_25, 0, x_69);
x_70 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_MessageData_ofFormat(x_63);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_2);
x_76 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_2, x_75, x_8, x_9, x_10, x_11, x_64);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_16 = x_78;
x_17 = x_77;
goto block_22;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_25);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_79 = lean_ctor_get(x_62, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_62, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_81 = x_62;
} else {
 lean_dec_ref(x_62);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_25, 1);
lean_inc(x_83);
lean_dec(x_25);
x_84 = lean_ctor_get(x_26, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_85 = x_26;
} else {
 lean_dec_ref(x_26);
 x_85 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
x_86 = l_Lean_Compiler_LCNF_ppDecl_x27(x_84, x_10, x_11, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Compiler_LCNF_Decl_size(x_15);
lean_dec(x_15);
x_90 = l___private_Init_Data_Repr_0__Nat_reprFast(x_89);
if (lean_is_scalar(x_85)) {
 x_91 = lean_alloc_ctor(3, 1, 0);
} else {
 x_91 = x_85;
 lean_ctor_set_tag(x_91, 3);
}
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_MessageData_ofFormat(x_91);
x_93 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_MessageData_ofFormat(x_87);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_2);
x_101 = l_Lean_addTrace___at_Lean_Compiler_LCNF_PassManager_run___spec__7(x_2, x_100, x_8, x_9, x_10, x_11, x_88);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9;
x_16 = x_103;
x_17 = x_102;
goto block_22;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_85);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_104 = lean_ctor_get(x_86, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_86, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_106 = x_86;
} else {
 lean_dec_ref(x_86);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_18;
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_IR_toIR(x_1, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_12);
x_18 = lean_ir_compile(x_17, x_2, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_size(x_19);
x_22 = lean_box(0);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8(x_19, x_3, x_19, x_21, x_4, x_22, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_12);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_ctor_set_tag(x_20, 3);
x_26 = l_Lean_MessageData_ofFormat(x_20);
x_27 = l_Lean_throwError___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_26, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_MessageData_ofFormat(x_29);
x_31 = l_Lean_throwError___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_30, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = l_Lean_setEnv___at_Lean_Compiler_LCNF_PassManager_run___spec__10(x_33, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_9);
lean_dec(x_8);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_12);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_compiler_enableNew;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1;
x_13 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = l_Lean_Compiler_LCNF_PassManager_run___lambda__1(x_1, x_11, x_2, x_3, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_1);
x_10 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1(x_9, x_10, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_markRecDecls(x_12);
x_15 = l_Lean_Compiler_LCNF_getPassManager___rarg(x_7, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_array_size(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6(x_18, x_16, x_16, x_19, x_10, x_14, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__2;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_23, x_4, x_5, x_6, x_7, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2(x_21, x_18, x_10, x_2, x_28, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_21);
return x_29;
}
else
{
lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_array_size(x_21);
x_32 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11(x_21, x_23, x_18, x_21, x_31, x_10, x_32, x_4, x_5, x_6, x_7, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2(x_21, x_18, x_10, x_2, x_32, x_4, x_5, x_6, x_7, x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_21);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
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
}
else
{
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_IR_toIR(x_1, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_12);
x_18 = lean_ir_compile(x_17, x_2, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_size(x_19);
x_22 = lean_box(0);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__14(x_19, x_3, x_19, x_21, x_4, x_22, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_12);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_ctor_set_tag(x_20, 3);
x_26 = l_Lean_MessageData_ofFormat(x_20);
x_27 = l_Lean_throwError___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_26, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_MessageData_ofFormat(x_29);
x_31 = l_Lean_throwError___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_30, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = l_Lean_setEnv___at_Lean_Compiler_LCNF_PassManager_run___spec__10(x_33, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_9);
lean_dec(x_8);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_12);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__5(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1;
x_13 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = l_Lean_Compiler_LCNF_PassManager_run___lambda__4(x_1, x_11, x_2, x_3, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_1);
x_10 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_PassManager_run___spec__1(x_9, x_10, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_markRecDecls(x_12);
x_15 = l_Lean_Compiler_LCNF_getPassManager___rarg(x_7, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_array_size(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__13(x_18, x_16, x_16, x_19, x_10, x_14, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__2;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___spec__1(x_23, x_4, x_5, x_6, x_7, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_LCNF_PassManager_run___lambda__5(x_21, x_18, x_10, x_2, x_28, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_21);
return x_29;
}
else
{
lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_array_size(x_21);
x_32 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__15(x_21, x_23, x_18, x_21, x_31, x_10, x_32, x_4, x_5, x_6, x_7, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Compiler_LCNF_PassManager_run___lambda__5(x_21, x_18, x_10, x_2, x_32, x_4, x_5, x_6, x_7, x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_21);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
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
}
else
{
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_23; 
lean_dec(x_7);
x_23 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_14 = x_23;
x_15 = x_6;
goto block_22;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_7, x_7);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_7);
x_25 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_14 = x_25;
x_15 = x_6;
goto block_22;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_28 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__12(x_1, x_26, x_27, x_28, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_14 = x_30;
x_15 = x_31;
goto block_22;
}
else
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
block_22:
{
uint8_t x_16; 
x_16 = l_Array_isEmpty___rarg(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_18 = lean_box(0);
x_19 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3(x_14, x_17, x_18, x_2, x_3, x_4, x_5, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
if (x_9 == 0)
{
lean_object* x_45; 
lean_dec(x_7);
x_45 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_36 = x_45;
x_37 = x_6;
goto block_44;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_7, x_7);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_7);
x_47 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_36 = x_47;
x_37 = x_6;
goto block_44;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_50 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
lean_inc(x_5);
lean_inc(x_4);
x_51 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__12(x_1, x_48, x_49, x_50, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_36 = x_52;
x_37 = x_53;
goto block_44;
}
else
{
uint8_t x_54; 
lean_dec(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
block_44:
{
uint8_t x_38; 
x_38 = l_Array_isEmpty___rarg(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_40 = lean_box(0);
x_41 = l_Lean_Compiler_LCNF_PassManager_run___lambda__6(x_36, x_39, x_40, x_2, x_3, x_4, x_5, x_37);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_36);
lean_dec(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_42 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_58 = lean_ctor_get(x_4, 0);
x_59 = lean_ctor_get(x_4, 1);
x_60 = lean_ctor_get(x_4, 2);
x_61 = lean_ctor_get(x_4, 3);
x_62 = lean_ctor_get(x_4, 4);
x_63 = lean_ctor_get(x_4, 5);
x_64 = lean_ctor_get(x_4, 6);
x_65 = lean_ctor_get(x_4, 7);
x_66 = lean_ctor_get(x_4, 8);
x_67 = lean_ctor_get(x_4, 9);
x_68 = lean_ctor_get(x_4, 10);
x_69 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_70 = lean_ctor_get(x_4, 11);
x_71 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_72 = lean_ctor_get(x_4, 12);
lean_inc(x_72);
lean_inc(x_70);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_4);
x_73 = lean_unsigned_to_nat(8192u);
x_74 = lean_nat_dec_le(x_73, x_62);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_62);
x_75 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_75, 0, x_58);
lean_ctor_set(x_75, 1, x_59);
lean_ctor_set(x_75, 2, x_60);
lean_ctor_set(x_75, 3, x_61);
lean_ctor_set(x_75, 4, x_73);
lean_ctor_set(x_75, 5, x_63);
lean_ctor_set(x_75, 6, x_64);
lean_ctor_set(x_75, 7, x_65);
lean_ctor_set(x_75, 8, x_66);
lean_ctor_set(x_75, 9, x_67);
lean_ctor_set(x_75, 10, x_68);
lean_ctor_set(x_75, 11, x_70);
lean_ctor_set(x_75, 12, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*13, x_69);
lean_ctor_set_uint8(x_75, sizeof(void*)*13 + 1, x_71);
if (x_9 == 0)
{
lean_object* x_85; 
lean_dec(x_7);
x_85 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_76 = x_85;
x_77 = x_6;
goto block_84;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_7, x_7);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_7);
x_87 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_76 = x_87;
x_77 = x_6;
goto block_84;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = 0;
x_89 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_90 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
lean_inc(x_5);
lean_inc(x_75);
x_91 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__12(x_1, x_88, x_89, x_90, x_2, x_3, x_75, x_5, x_6);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_76 = x_92;
x_77 = x_93;
goto block_84;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_75);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
block_84:
{
uint8_t x_78; 
x_78 = l_Array_isEmpty___rarg(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_80 = lean_box(0);
x_81 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3(x_76, x_79, x_80, x_2, x_3, x_75, x_5, x_77);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_82 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_98, 0, x_58);
lean_ctor_set(x_98, 1, x_59);
lean_ctor_set(x_98, 2, x_60);
lean_ctor_set(x_98, 3, x_61);
lean_ctor_set(x_98, 4, x_62);
lean_ctor_set(x_98, 5, x_63);
lean_ctor_set(x_98, 6, x_64);
lean_ctor_set(x_98, 7, x_65);
lean_ctor_set(x_98, 8, x_66);
lean_ctor_set(x_98, 9, x_67);
lean_ctor_set(x_98, 10, x_68);
lean_ctor_set(x_98, 11, x_70);
lean_ctor_set(x_98, 12, x_72);
lean_ctor_set_uint8(x_98, sizeof(void*)*13, x_69);
lean_ctor_set_uint8(x_98, sizeof(void*)*13 + 1, x_71);
if (x_9 == 0)
{
lean_object* x_108; 
lean_dec(x_7);
x_108 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_99 = x_108;
x_100 = x_6;
goto block_107;
}
else
{
uint8_t x_109; 
x_109 = lean_nat_dec_le(x_7, x_7);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_7);
x_110 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_99 = x_110;
x_100 = x_6;
goto block_107;
}
else
{
size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; 
x_111 = 0;
x_112 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_113 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
lean_inc(x_5);
lean_inc(x_98);
x_114 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__12(x_1, x_111, x_112, x_113, x_2, x_3, x_98, x_5, x_6);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_99 = x_115;
x_100 = x_116;
goto block_107;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
block_107:
{
uint8_t x_101; 
x_101 = l_Array_isEmpty___rarg(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_103 = lean_box(0);
x_104 = l_Lean_Compiler_LCNF_PassManager_run___lambda__6(x_99, x_102, x_103, x_2, x_3, x_98, x_5, x_100);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_105 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_100);
return x_106;
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; double x_18; double x_19; lean_object* x_20; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox_float(x_8);
lean_dec(x_8);
x_19 = lean_unbox_float(x_9);
lean_dec(x_9);
x_20 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2(x_1, x_16, x_3, x_4, x_5, x_6, x_17, x_18, x_19, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; double x_18; double x_19; lean_object* x_20; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox_float(x_7);
lean_dec(x_7);
x_19 = lean_unbox_float(x_8);
lean_dec(x_8);
x_20 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3(x_1, x_16, x_3, x_4, x_5, x_17, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_20;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_PassManager_run___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_PassManager_run___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_PassManager_run___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at_Lean_Compiler_LCNF_PassManager_run___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_PassManager_run___spec__12(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__13(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__14(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__15(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Lean_Compiler_LCNF_PassManager_run___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Lean_Compiler_LCNF_PassManager_run___lambda__2(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Lean_Compiler_LCNF_PassManager_run___lambda__4(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Lean_Compiler_LCNF_PassManager_run___lambda__5(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_PassManager_run___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_compile___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_compile___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_compile___closed__3;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_compile___closed__4;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassManager_run___boxed), 6, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Compiler_LCNF_compile___closed__5;
x_7 = 0;
x_8 = l_Lean_Compiler_LCNF_CompilerM_run___rarg(x_5, x_6, x_7, x_2, x_3, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_showDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<not-available>", 15, 15);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Compiler_LCNF_showDecl(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_7);
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(x_1, x_5, x_2, x_3, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(x_4, x_7, x_8, x_11);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_7 == 0)
{
double x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set_float(x_15, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_15, sizeof(void*)*2 + 8, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 16, x_2);
x_16 = lean_box(0);
x_17 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__1(x_4, x_5, x_10, x_6, x_15, x_16, x_11, x_12, x_13);
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
x_20 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__1(x_4, x_5, x_10, x_6, x_18, x_19, x_11, x_12, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, double x_7, double x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_18 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_16, x_11, x_12, x_17);
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
x_20 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__3___closed__2;
x_21 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_20, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_5);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__1;
x_16 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_io_mono_nanos_now(x_14);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_10);
lean_inc(x_9);
x_115 = lean_apply_3(x_7, x_9, x_10, x_114);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_117);
x_120 = lean_io_mono_nanos_now(x_118);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; double x_126; double x_127; double x_128; double x_129; double x_130; lean_object* x_131; lean_object* x_132; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
x_124 = 0;
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Float_ofScientific(x_113, x_124, x_125);
lean_dec(x_113);
x_127 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_128 = lean_float_div(x_126, x_127);
x_129 = l_Float_ofScientific(x_122, x_124, x_125);
lean_dec(x_122);
x_130 = lean_float_div(x_129, x_127);
x_131 = lean_box_float(x_128);
x_132 = lean_box_float(x_130);
lean_ctor_set(x_120, 1, x_132);
lean_ctor_set(x_120, 0, x_131);
lean_ctor_set(x_115, 1, x_120);
lean_ctor_set(x_115, 0, x_119);
x_17 = x_115;
x_18 = x_123;
goto block_111;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; double x_137; double x_138; double x_139; double x_140; double x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_133 = lean_ctor_get(x_120, 0);
x_134 = lean_ctor_get(x_120, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_120);
x_135 = 0;
x_136 = lean_unsigned_to_nat(0u);
x_137 = l_Float_ofScientific(x_113, x_135, x_136);
lean_dec(x_113);
x_138 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_139 = lean_float_div(x_137, x_138);
x_140 = l_Float_ofScientific(x_133, x_135, x_136);
lean_dec(x_133);
x_141 = lean_float_div(x_140, x_138);
x_142 = lean_box_float(x_139);
x_143 = lean_box_float(x_141);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_115, 1, x_144);
lean_ctor_set(x_115, 0, x_119);
x_17 = x_115;
x_18 = x_134;
goto block_111;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; double x_154; double x_155; double x_156; double x_157; double x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_145 = lean_ctor_get(x_115, 0);
x_146 = lean_ctor_get(x_115, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_115);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_145);
x_148 = lean_io_mono_nanos_now(x_146);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = 0;
x_153 = lean_unsigned_to_nat(0u);
x_154 = l_Float_ofScientific(x_113, x_152, x_153);
lean_dec(x_113);
x_155 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_156 = lean_float_div(x_154, x_155);
x_157 = l_Float_ofScientific(x_149, x_152, x_153);
lean_dec(x_149);
x_158 = lean_float_div(x_157, x_155);
x_159 = lean_box_float(x_156);
x_160 = lean_box_float(x_158);
if (lean_is_scalar(x_151)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_151;
}
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_147);
lean_ctor_set(x_162, 1, x_161);
x_17 = x_162;
x_18 = x_150;
goto block_111;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_115);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_164 = lean_ctor_get(x_115, 0);
x_165 = lean_ctor_get(x_115, 1);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_164);
x_167 = lean_io_mono_nanos_now(x_165);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; double x_173; double x_174; double x_175; double x_176; double x_177; lean_object* x_178; lean_object* x_179; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ctor_get(x_167, 1);
x_171 = 0;
x_172 = lean_unsigned_to_nat(0u);
x_173 = l_Float_ofScientific(x_113, x_171, x_172);
lean_dec(x_113);
x_174 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_175 = lean_float_div(x_173, x_174);
x_176 = l_Float_ofScientific(x_169, x_171, x_172);
lean_dec(x_169);
x_177 = lean_float_div(x_176, x_174);
x_178 = lean_box_float(x_175);
x_179 = lean_box_float(x_177);
lean_ctor_set(x_167, 1, x_179);
lean_ctor_set(x_167, 0, x_178);
lean_ctor_set_tag(x_115, 0);
lean_ctor_set(x_115, 1, x_167);
lean_ctor_set(x_115, 0, x_166);
x_17 = x_115;
x_18 = x_170;
goto block_111;
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; double x_184; double x_185; double x_186; double x_187; double x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_180 = lean_ctor_get(x_167, 0);
x_181 = lean_ctor_get(x_167, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_167);
x_182 = 0;
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Float_ofScientific(x_113, x_182, x_183);
lean_dec(x_113);
x_185 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_186 = lean_float_div(x_184, x_185);
x_187 = l_Float_ofScientific(x_180, x_182, x_183);
lean_dec(x_180);
x_188 = lean_float_div(x_187, x_185);
x_189 = lean_box_float(x_186);
x_190 = lean_box_float(x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set_tag(x_115, 0);
lean_ctor_set(x_115, 1, x_191);
lean_ctor_set(x_115, 0, x_166);
x_17 = x_115;
x_18 = x_181;
goto block_111;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; double x_201; double x_202; double x_203; double x_204; double x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_192 = lean_ctor_get(x_115, 0);
x_193 = lean_ctor_get(x_115, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_115);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_192);
x_195 = lean_io_mono_nanos_now(x_193);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
x_199 = 0;
x_200 = lean_unsigned_to_nat(0u);
x_201 = l_Float_ofScientific(x_113, x_199, x_200);
lean_dec(x_113);
x_202 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__5;
x_203 = lean_float_div(x_201, x_202);
x_204 = l_Float_ofScientific(x_196, x_199, x_200);
lean_dec(x_196);
x_205 = lean_float_div(x_204, x_202);
x_206 = lean_box_float(x_203);
x_207 = lean_box_float(x_205);
if (lean_is_scalar(x_198)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_198;
}
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_194);
lean_ctor_set(x_209, 1, x_208);
x_17 = x_209;
x_18 = x_197;
goto block_111;
}
}
block_111:
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
x_23 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
x_24 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_1, x_23);
if (x_24 == 0)
{
if (x_6 == 0)
{
uint8_t x_91; 
x_91 = 0;
x_25 = x_91;
goto block_90;
}
else
{
lean_object* x_92; double x_93; double x_94; lean_object* x_95; 
x_92 = lean_box(0);
x_93 = lean_unbox_float(x_21);
lean_dec(x_21);
x_94 = lean_unbox_float(x_22);
lean_dec(x_22);
x_95 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_93, x_94, x_5, x_92, x_9, x_10, x_18);
return x_95;
}
}
else
{
if (x_6 == 0)
{
double x_96; double x_97; double x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; double x_103; double x_104; double x_105; uint8_t x_106; 
x_96 = lean_unbox_float(x_22);
x_97 = lean_unbox_float(x_21);
x_98 = lean_float_sub(x_96, x_97);
x_99 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3;
x_100 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_99);
x_101 = 0;
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Float_ofScientific(x_100, x_101, x_102);
lean_dec(x_100);
x_104 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__4;
x_105 = lean_float_div(x_103, x_104);
x_106 = lean_float_decLt(x_105, x_98);
x_25 = x_106;
goto block_90;
}
else
{
lean_object* x_107; double x_108; double x_109; lean_object* x_110; 
x_107 = lean_box(0);
x_108 = lean_unbox_float(x_21);
lean_dec(x_21);
x_109 = lean_unbox_float(x_22);
lean_dec(x_22);
x_110 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_108, x_109, x_5, x_107, x_9, x_10, x_18);
return x_110;
}
}
block_90:
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
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 4);
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
x_37 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(x_20, x_9, x_10, x_36);
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
lean_ctor_set(x_27, 4, x_49);
x_50 = lean_st_ref_set(x_10, x_27, x_29);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(x_20, x_9, x_10, x_51);
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
x_63 = lean_ctor_get(x_27, 2);
x_64 = lean_ctor_get(x_27, 3);
x_65 = lean_ctor_get(x_27, 5);
x_66 = lean_ctor_get(x_27, 6);
x_67 = lean_ctor_get(x_27, 7);
x_68 = lean_ctor_get(x_27, 8);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_69 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_70 = lean_ctor_get(x_28, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_71 = x_28;
} else {
 lean_dec_ref(x_28);
 x_71 = lean_box(0);
}
x_72 = l_Lean_PersistentArray_append___rarg(x_13, x_70);
lean_dec(x_70);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 1, 8);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_uint64(x_73, sizeof(void*)*1, x_69);
x_74 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set(x_74, 1, x_62);
lean_ctor_set(x_74, 2, x_63);
lean_ctor_set(x_74, 3, x_64);
lean_ctor_set(x_74, 4, x_73);
lean_ctor_set(x_74, 5, x_65);
lean_ctor_set(x_74, 6, x_66);
lean_ctor_set(x_74, 7, x_67);
lean_ctor_set(x_74, 8, x_68);
x_75 = lean_st_ref_set(x_10, x_74, x_29);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(x_20, x_9, x_10, x_76);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
lean_object* x_86; double x_87; double x_88; lean_object* x_89; 
x_86 = lean_box(0);
x_87 = lean_unbox_float(x_21);
lean_dec(x_21);
x_88 = lean_unbox_float(x_22);
lean_dec(x_22);
x_89 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_87, x_88, x_5, x_86, x_9, x_10, x_18);
return x_89;
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_io_get_num_heartbeats(x_14);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
lean_inc(x_10);
lean_inc(x_9);
x_306 = lean_apply_3(x_7, x_9, x_10, x_305);
if (lean_obj_tag(x_306) == 0)
{
uint8_t x_307; 
x_307 = !lean_is_exclusive(x_306);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_308 = lean_ctor_get(x_306, 0);
x_309 = lean_ctor_get(x_306, 1);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_308);
x_311 = lean_io_get_num_heartbeats(x_309);
x_312 = !lean_is_exclusive(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; double x_317; double x_318; lean_object* x_319; lean_object* x_320; 
x_313 = lean_ctor_get(x_311, 0);
x_314 = lean_ctor_get(x_311, 1);
x_315 = 0;
x_316 = lean_unsigned_to_nat(0u);
x_317 = l_Float_ofScientific(x_304, x_315, x_316);
lean_dec(x_304);
x_318 = l_Float_ofScientific(x_313, x_315, x_316);
lean_dec(x_313);
x_319 = lean_box_float(x_317);
x_320 = lean_box_float(x_318);
lean_ctor_set(x_311, 1, x_320);
lean_ctor_set(x_311, 0, x_319);
lean_ctor_set(x_306, 1, x_311);
lean_ctor_set(x_306, 0, x_310);
x_210 = x_306;
x_211 = x_314;
goto block_302;
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; double x_325; double x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_321 = lean_ctor_get(x_311, 0);
x_322 = lean_ctor_get(x_311, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_311);
x_323 = 0;
x_324 = lean_unsigned_to_nat(0u);
x_325 = l_Float_ofScientific(x_304, x_323, x_324);
lean_dec(x_304);
x_326 = l_Float_ofScientific(x_321, x_323, x_324);
lean_dec(x_321);
x_327 = lean_box_float(x_325);
x_328 = lean_box_float(x_326);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
lean_ctor_set(x_306, 1, x_329);
lean_ctor_set(x_306, 0, x_310);
x_210 = x_306;
x_211 = x_322;
goto block_302;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; double x_339; double x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_330 = lean_ctor_get(x_306, 0);
x_331 = lean_ctor_get(x_306, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_306);
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_330);
x_333 = lean_io_get_num_heartbeats(x_331);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_336 = x_333;
} else {
 lean_dec_ref(x_333);
 x_336 = lean_box(0);
}
x_337 = 0;
x_338 = lean_unsigned_to_nat(0u);
x_339 = l_Float_ofScientific(x_304, x_337, x_338);
lean_dec(x_304);
x_340 = l_Float_ofScientific(x_334, x_337, x_338);
lean_dec(x_334);
x_341 = lean_box_float(x_339);
x_342 = lean_box_float(x_340);
if (lean_is_scalar(x_336)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_336;
}
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_332);
lean_ctor_set(x_344, 1, x_343);
x_210 = x_344;
x_211 = x_335;
goto block_302;
}
}
else
{
uint8_t x_345; 
x_345 = !lean_is_exclusive(x_306);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
x_346 = lean_ctor_get(x_306, 0);
x_347 = lean_ctor_get(x_306, 1);
x_348 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_348, 0, x_346);
x_349 = lean_io_get_num_heartbeats(x_347);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; double x_355; double x_356; lean_object* x_357; lean_object* x_358; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_ctor_get(x_349, 1);
x_353 = 0;
x_354 = lean_unsigned_to_nat(0u);
x_355 = l_Float_ofScientific(x_304, x_353, x_354);
lean_dec(x_304);
x_356 = l_Float_ofScientific(x_351, x_353, x_354);
lean_dec(x_351);
x_357 = lean_box_float(x_355);
x_358 = lean_box_float(x_356);
lean_ctor_set(x_349, 1, x_358);
lean_ctor_set(x_349, 0, x_357);
lean_ctor_set_tag(x_306, 0);
lean_ctor_set(x_306, 1, x_349);
lean_ctor_set(x_306, 0, x_348);
x_210 = x_306;
x_211 = x_352;
goto block_302;
}
else
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; double x_363; double x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_359 = lean_ctor_get(x_349, 0);
x_360 = lean_ctor_get(x_349, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_349);
x_361 = 0;
x_362 = lean_unsigned_to_nat(0u);
x_363 = l_Float_ofScientific(x_304, x_361, x_362);
lean_dec(x_304);
x_364 = l_Float_ofScientific(x_359, x_361, x_362);
lean_dec(x_359);
x_365 = lean_box_float(x_363);
x_366 = lean_box_float(x_364);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
lean_ctor_set_tag(x_306, 0);
lean_ctor_set(x_306, 1, x_367);
lean_ctor_set(x_306, 0, x_348);
x_210 = x_306;
x_211 = x_360;
goto block_302;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; double x_377; double x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_368 = lean_ctor_get(x_306, 0);
x_369 = lean_ctor_get(x_306, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_306);
x_370 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_370, 0, x_368);
x_371 = lean_io_get_num_heartbeats(x_369);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_374 = x_371;
} else {
 lean_dec_ref(x_371);
 x_374 = lean_box(0);
}
x_375 = 0;
x_376 = lean_unsigned_to_nat(0u);
x_377 = l_Float_ofScientific(x_304, x_375, x_376);
lean_dec(x_304);
x_378 = l_Float_ofScientific(x_372, x_375, x_376);
lean_dec(x_372);
x_379 = lean_box_float(x_377);
x_380 = lean_box_float(x_378);
if (lean_is_scalar(x_374)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_374;
}
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_370);
lean_ctor_set(x_382, 1, x_381);
x_210 = x_382;
x_211 = x_373;
goto block_302;
}
}
block_302:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_218; 
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
lean_dec(x_210);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_dec(x_212);
x_216 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
x_217 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_1, x_216);
if (x_217 == 0)
{
if (x_6 == 0)
{
uint8_t x_284; 
x_284 = 0;
x_218 = x_284;
goto block_283;
}
else
{
lean_object* x_285; double x_286; double x_287; lean_object* x_288; 
x_285 = lean_box(0);
x_286 = lean_unbox_float(x_214);
lean_dec(x_214);
x_287 = lean_unbox_float(x_215);
lean_dec(x_215);
x_288 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_213, x_217, x_286, x_287, x_5, x_285, x_9, x_10, x_211);
return x_288;
}
}
else
{
if (x_6 == 0)
{
double x_289; double x_290; double x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; double x_296; uint8_t x_297; 
x_289 = lean_unbox_float(x_215);
x_290 = lean_unbox_float(x_214);
x_291 = lean_float_sub(x_289, x_290);
x_292 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__3;
x_293 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__1(x_1, x_292);
x_294 = 0;
x_295 = lean_unsigned_to_nat(0u);
x_296 = l_Float_ofScientific(x_293, x_294, x_295);
lean_dec(x_293);
x_297 = lean_float_decLt(x_296, x_291);
x_218 = x_297;
goto block_283;
}
else
{
lean_object* x_298; double x_299; double x_300; lean_object* x_301; 
x_298 = lean_box(0);
x_299 = lean_unbox_float(x_214);
lean_dec(x_214);
x_300 = lean_unbox_float(x_215);
lean_dec(x_215);
x_301 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_213, x_217, x_299, x_300, x_5, x_298, x_9, x_10, x_211);
return x_301;
}
}
block_283:
{
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_219 = lean_st_ref_take(x_10, x_211);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_220, 4);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
x_223 = !lean_is_exclusive(x_220);
if (x_223 == 0)
{
lean_object* x_224; uint8_t x_225; 
x_224 = lean_ctor_get(x_220, 4);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_221);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_221, 0);
x_227 = l_Lean_PersistentArray_append___rarg(x_13, x_226);
lean_dec(x_226);
lean_ctor_set(x_221, 0, x_227);
x_228 = lean_st_ref_set(x_10, x_220, x_222);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(x_213, x_9, x_10, x_229);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_213);
if (lean_obj_tag(x_230) == 0)
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
return x_230;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_230, 0);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_230);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
else
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_230);
if (x_235 == 0)
{
return x_230;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_230, 0);
x_237 = lean_ctor_get(x_230, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_230);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
uint64_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_239 = lean_ctor_get_uint64(x_221, sizeof(void*)*1);
x_240 = lean_ctor_get(x_221, 0);
lean_inc(x_240);
lean_dec(x_221);
x_241 = l_Lean_PersistentArray_append___rarg(x_13, x_240);
lean_dec(x_240);
x_242 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set_uint64(x_242, sizeof(void*)*1, x_239);
lean_ctor_set(x_220, 4, x_242);
x_243 = lean_st_ref_set(x_10, x_220, x_222);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(x_213, x_9, x_10, x_244);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_213);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_248 = x_245;
} else {
 lean_dec_ref(x_245);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_245, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_245, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_252 = x_245;
} else {
 lean_dec_ref(x_245);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint64_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_254 = lean_ctor_get(x_220, 0);
x_255 = lean_ctor_get(x_220, 1);
x_256 = lean_ctor_get(x_220, 2);
x_257 = lean_ctor_get(x_220, 3);
x_258 = lean_ctor_get(x_220, 5);
x_259 = lean_ctor_get(x_220, 6);
x_260 = lean_ctor_get(x_220, 7);
x_261 = lean_ctor_get(x_220, 8);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_220);
x_262 = lean_ctor_get_uint64(x_221, sizeof(void*)*1);
x_263 = lean_ctor_get(x_221, 0);
lean_inc(x_263);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_264 = x_221;
} else {
 lean_dec_ref(x_221);
 x_264 = lean_box(0);
}
x_265 = l_Lean_PersistentArray_append___rarg(x_13, x_263);
lean_dec(x_263);
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(0, 1, 8);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set_uint64(x_266, sizeof(void*)*1, x_262);
x_267 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_267, 0, x_254);
lean_ctor_set(x_267, 1, x_255);
lean_ctor_set(x_267, 2, x_256);
lean_ctor_set(x_267, 3, x_257);
lean_ctor_set(x_267, 4, x_266);
lean_ctor_set(x_267, 5, x_258);
lean_ctor_set(x_267, 6, x_259);
lean_ctor_set(x_267, 7, x_260);
lean_ctor_set(x_267, 8, x_261);
x_268 = lean_st_ref_set(x_10, x_267, x_222);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_270 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(x_213, x_9, x_10, x_269);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_213);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_270, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_270, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_277 = x_270;
} else {
 lean_dec_ref(x_270);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
else
{
lean_object* x_279; double x_280; double x_281; lean_object* x_282; 
x_279 = lean_box(0);
x_280 = lean_unbox_float(x_214);
lean_dec(x_214);
x_281 = lean_unbox_float(x_215);
lean_dec(x_215);
x_282 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3(x_2, x_3, x_4, x_13, x_213, x_217, x_280, x_281, x_5, x_279, x_9, x_10, x_211);
return x_282;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_14 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__4___closed__2;
x_15 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_9, x_14);
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
x_27 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__4(x_9, x_1, x_4, x_5, x_2, x_26, x_3, x_25, x_6, x_7, x_13);
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
x_31 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__4(x_9, x_1, x_4, x_5, x_2, x_30, x_3, x_29, x_6, x_7, x_28);
lean_dec(x_9);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiling new: ", 15, 15);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at_Lean_compileDecls_doCompile___spec__1(x_1, x_6);
x_8 = l_Lean_MessageData_ofList(x_7);
x_9 = l_Lean_Compiler_LCNF_main___lambda__1___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_1 = lean_mk_string_unchecked("compilation new", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_lcnf_compile_decls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_main___lambda__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_array_mk(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_main___lambda__2___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Compiler_LCNF_compile___closed__5;
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CompilerM_run___rarg___boxed), 6, 3);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2;
x_14 = 1;
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6;
x_16 = lean_box(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___boxed), 8, 5);
lean_closure_set(x_17, 0, x_13);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_12);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_15);
x_18 = l_Lean_Compiler_LCNF_main___closed__1;
x_19 = lean_box(0);
x_20 = l_Lean_profileitM___at_Lean_traceBlock___spec__1___rarg(x_18, x_5, x_17, x_19, x_2, x_3, x_4);
lean_dec(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_MonadExcept_ofExcept___at_Lean_Compiler_LCNF_main___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_18 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__2(x_1, x_14, x_3, x_4, x_5, x_6, x_15, x_16, x_17, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_18 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__3(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___lambda__4(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_main___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__4;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__11;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__12;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__13;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__14;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__16;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__18;
x_2 = lean_unsigned_to_nat(1689u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("test", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__20;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("jp", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__22;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__2;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__19;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__21;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__2;
x_11 = l_Lean_registerTraceClass(x_10, x_3, x_4, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__23;
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
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Compiler_ExternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Checker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIR(builtin, lean_io_mk_world());
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
l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___closed__1 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___lambda__4___closed__1);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1);
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2();
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
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__2___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__8);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___lambda__3___closed__9);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_checkpoint___spec__1___closed__4);
l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Compiler_LCNF_PassManager_run___spec__2___lambda__2___closed__1();
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
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__8);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__9);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__10);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__11);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__12);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__13);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__14);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__15);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__16);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__17);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__18);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__6___lambda__1___closed__19);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__8___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_PassManager_run___spec__11___closed__4);
l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___lambda__2___closed__1);
l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__1 = _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__1);
l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__2 = _init_l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___lambda__3___closed__2);
l_Lean_Compiler_LCNF_compile___closed__1 = _init_l_Lean_Compiler_LCNF_compile___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__1);
l_Lean_Compiler_LCNF_compile___closed__2 = _init_l_Lean_Compiler_LCNF_compile___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__2);
l_Lean_Compiler_LCNF_compile___closed__3 = _init_l_Lean_Compiler_LCNF_compile___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__3);
l_Lean_Compiler_LCNF_compile___closed__4 = _init_l_Lean_Compiler_LCNF_compile___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__4);
l_Lean_Compiler_LCNF_compile___closed__5 = _init_l_Lean_Compiler_LCNF_compile___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__5);
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
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__17);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__18 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__18);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__19 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__19);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__20 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__20);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__21 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__21);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__22 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__22);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__23 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689____closed__23);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1689_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
