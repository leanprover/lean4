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
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__19;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__10;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_compile___closed__1;
static lean_object* l_Lean_Compiler_LCNF_isValidMainType___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__8;
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_isValidMainType___closed__3;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__1;
static lean_object* l_Lean_Compiler_LCNF_compile___closed__5;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__2;
uint8_t l_Lean_Compiler_hasMacroInlineAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__21;
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
lean_object* lean_io_get_num_heartbeats(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_getImplementedBy_x3f(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* lean_lcnf_compile_decls(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__24;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__4;
lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__15;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__4;
static uint64_t l_Lean_Compiler_LCNF_shouldGenerateCode___closed__20;
static lean_object* l_Lean_Compiler_LCNF_compile___closed__4;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_showDecl___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__27;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__14;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_main___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7;
lean_object* lean_nat_div(lean_object*, lean_object*);
static double l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__0;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__1;
lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__13;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__23;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2;
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(size_t, size_t, lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___closed__0;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isValidMainType(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__2;
static lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__7;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_main___lam__0___closed__0;
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__6;
lean_object* l_Lean_Compiler_LCNF_markRecDecls(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__6;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
uint8_t l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__16;
static lean_object* l_Lean_Compiler_LCNF_compile___closed__2;
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_2012_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__20;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__18;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__12;
extern lean_object* l_Lean_Compiler_compiler_check;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_compile___closed__6;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_isValidMainType___closed__1;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6;
static lean_object* l_Lean_Compiler_LCNF_showDecl___closed__0;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__17;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_isValidMainType___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_isValidMainType___closed__5;
static lean_object* l_Lean_Compiler_LCNF_main___lam__0___closed__1;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__26;
static lean_object* l_Lean_Compiler_LCNF_isValidMainType___closed__7;
static lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__4;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8;
static lean_object* l_Lean_Compiler_LCNF_isValidMainType___closed__6;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
static lean_object* l_Lean_Compiler_LCNF_PassManager_run___closed__4;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isValidMainType___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_compile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_size(lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__16;
lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
static lean_object* l_Lean_Compiler_LCNF_compile___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__15;
lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_isValidMainType___closed__4;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__25;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__1;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__3;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12;
static lean_object* l_Lean_Compiler_LCNF_compile___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__18;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
static double l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__3;
static lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__19;
double lean_float_sub(double, double);
static lean_object* l_Lean_Compiler_LCNF_isValidMainType___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Meta_isProp(x_10, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = l_Lean_Meta_isTypeFormerType(x_10, x_2, x_3, x_4, x_5, x_14);
return x_15;
}
else
{
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_is_matcher(x_7, x_1);
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
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = lean_is_matcher(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__6;
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__5;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__4;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__3;
x_5 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__2;
x_6 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1;
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
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__11;
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__10;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__9;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__8;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__15() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__14;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__16;
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__17;
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__15;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__12;
x_5 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__19() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 2;
x_2 = 0;
x_3 = 1;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_6, 0, x_5);
lean_ctor_set_uint8(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, 2, x_5);
lean_ctor_set_uint8(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, 4, x_5);
lean_ctor_set_uint8(x_6, 5, x_4);
lean_ctor_set_uint8(x_6, 6, x_4);
lean_ctor_set_uint8(x_6, 7, x_5);
lean_ctor_set_uint8(x_6, 8, x_4);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_2);
lean_ctor_set_uint8(x_6, 11, x_4);
lean_ctor_set_uint8(x_6, 12, x_4);
lean_ctor_set_uint8(x_6, 13, x_4);
lean_ctor_set_uint8(x_6, 14, x_1);
lean_ctor_set_uint8(x_6, 15, x_4);
lean_ctor_set_uint8(x_6, 16, x_4);
lean_ctor_set_uint8(x_6, 17, x_4);
lean_ctor_set_uint8(x_6, 18, x_4);
return x_6;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__20() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__19;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__21() {
_start:
{
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__20;
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__19;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__24() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__13;
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__23;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__24;
x_3 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__22;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__26;
x_5 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__25;
x_6 = lean_box(1);
x_7 = 0;
x_8 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__21;
x_9 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_3);
lean_ctor_set(x_9, 5, x_2);
lean_ctor_set(x_9, 6, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*7, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 2, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_78; lean_object* x_79; 
x_5 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__18;
x_6 = lean_st_mk_ref(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = 0;
x_38 = 1;
x_78 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__27;
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_1);
x_79 = l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(x_1, x_78, x_7, x_2, x_3, x_8);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_st_ref_get(x_7, x_81);
lean_dec(x_7);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_unbox(x_80);
lean_dec(x_80);
x_39 = x_84;
x_40 = x_83;
goto block_77;
}
else
{
lean_dec(x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec_ref(x_79);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_39 = x_87;
x_40 = x_86;
goto block_77;
}
else
{
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_79;
}
}
block_37:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_9);
lean_inc(x_1);
x_15 = l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(x_1, x_3, x_13);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = l_Lean_isCasesOnRecursor(x_11, x_1);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_box(x_12);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; 
x_22 = lean_box(x_10);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_isCasesOnRecursor(x_11, x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_12);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec_ref(x_11);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_15, 0);
lean_dec(x_30);
x_31 = lean_box(x_10);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_box(x_10);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_35 = lean_box(x_10);
if (lean_is_scalar(x_9)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_9;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_13);
return x_36;
}
}
block_77:
{
if (x_39 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_st_ref_get(x_3, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_45);
lean_dec(x_43);
lean_inc(x_1);
lean_inc_ref(x_45);
x_46 = l_Lean_isExtern(x_45, x_1);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_45);
x_47 = l_Lean_Environment_constants(x_45);
lean_inc(x_1);
x_48 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(x_47, x_1);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec_ref(x_45);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_box(x_10);
lean_ctor_set(x_41, 0, x_49);
return x_41;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Lean_ConstantInfo_hasValue(x_50, x_38);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec_ref(x_45);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_box(x_10);
lean_ctor_set(x_41, 0, x_52);
return x_41;
}
else
{
uint8_t x_53; 
lean_inc(x_1);
lean_inc_ref(x_45);
x_53 = l_Lean_Compiler_hasMacroInlineAttribute(x_45, x_1);
if (x_53 == 0)
{
lean_object* x_54; 
lean_free_object(x_41);
lean_inc(x_1);
lean_inc_ref(x_45);
x_54 = l_Lean_Compiler_getImplementedBy_x3f(x_45, x_1);
if (lean_obj_tag(x_54) == 0)
{
x_11 = x_45;
x_12 = x_51;
x_13 = x_44;
x_14 = x_53;
goto block_37;
}
else
{
lean_dec_ref(x_54);
x_11 = x_45;
x_12 = x_51;
x_13 = x_44;
x_14 = x_51;
goto block_37;
}
}
else
{
lean_object* x_55; 
lean_dec_ref(x_45);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_55 = lean_box(x_10);
lean_ctor_set(x_41, 0, x_55);
return x_41;
}
}
}
}
else
{
lean_object* x_56; 
lean_dec_ref(x_45);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_56 = lean_box(x_46);
lean_ctor_set(x_41, 0, x_56);
return x_41;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_41);
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
lean_dec(x_57);
lean_inc(x_1);
lean_inc_ref(x_59);
x_60 = l_Lean_isExtern(x_59, x_1);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_inc_ref(x_59);
x_61 = l_Lean_Environment_constants(x_59);
lean_inc(x_1);
x_62 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(x_61, x_1);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_59);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_box(x_10);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec_ref(x_62);
x_66 = l_Lean_ConstantInfo_hasValue(x_65, x_38);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_59);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_67 = lean_box(x_10);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_58);
return x_68;
}
else
{
uint8_t x_69; 
lean_inc(x_1);
lean_inc_ref(x_59);
x_69 = l_Lean_Compiler_hasMacroInlineAttribute(x_59, x_1);
if (x_69 == 0)
{
lean_object* x_70; 
lean_inc(x_1);
lean_inc_ref(x_59);
x_70 = l_Lean_Compiler_getImplementedBy_x3f(x_59, x_1);
if (lean_obj_tag(x_70) == 0)
{
x_11 = x_59;
x_12 = x_66;
x_13 = x_58;
x_14 = x_69;
goto block_37;
}
else
{
lean_dec_ref(x_70);
x_11 = x_59;
x_12 = x_66;
x_13 = x_58;
x_14 = x_66;
goto block_37;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_59);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_71 = lean_box(x_10);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_58);
return x_72;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_59);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_73 = lean_box(x_60);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_58);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_75 = lean_box(x_10);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_40);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Decl_check(x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stat", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("size: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__11;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pp", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motives", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pi", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__16;
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__15;
x_3 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__14;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; uint8_t x_148; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_192; 
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__2;
x_22 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__0___redArg(x_21, x_10, x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_array_uget(x_4, x_6);
x_192 = lean_unbox(x_23);
lean_dec(x_23);
if (x_192 == 0)
{
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_173 = x_8;
x_174 = x_9;
x_175 = x_10;
x_176 = x_11;
x_177 = x_24;
goto block_191;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_193 = lean_ctor_get(x_26, 0);
lean_inc(x_193);
x_194 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_195 = l_Lean_MessageData_ofName(x_193);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__20;
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_Compiler_LCNF_Decl_size(x_26);
x_200 = l_Nat_reprFast(x_199);
x_201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = l_Lean_MessageData_ofFormat(x_201);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_194);
x_205 = l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(x_21, x_204, x_9, x_10, x_11, x_24);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec_ref(x_205);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_173 = x_8;
x_174 = x_9;
x_175 = x_10;
x_176 = x_11;
x_177 = x_206;
goto block_191;
}
block_139:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_32, 4);
lean_dec(x_36);
x_37 = lean_ctor_get(x_32, 2);
lean_dec(x_37);
x_38 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__3;
x_39 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_27, x_38);
lean_ctor_set(x_32, 4, x_39);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*13, x_30);
lean_inc(x_28);
x_40 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__0___redArg(x_28, x_32, x_34);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_28);
lean_dec(x_25);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_1, x_31, x_29, x_32, x_33, x_43);
x_13 = x_44;
goto block_18;
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 1);
x_47 = lean_ctor_get(x_40, 0);
lean_dec(x_47);
lean_inc(x_33);
lean_inc_ref(x_32);
lean_inc_ref(x_26);
x_48 = l_Lean_Compiler_LCNF_ppDecl_x27(x_26, x_32, x_33, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5;
x_52 = l_Lean_Compiler_LCNF_Decl_size(x_26);
x_53 = l_Nat_reprFast(x_52);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_MessageData_ofFormat(x_54);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_55);
lean_ctor_set(x_40, 0, x_51);
x_56 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7;
if (lean_is_scalar(x_25)) {
 x_57 = lean_alloc_ctor(7, 2, 0);
} else {
 x_57 = x_25;
 lean_ctor_set_tag(x_57, 7);
}
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_49);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(x_28, x_61, x_29, x_32, x_33, x_50);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_63, x_31, x_29, x_32, x_33, x_64);
lean_dec(x_63);
x_13 = x_65;
goto block_18;
}
else
{
uint8_t x_66; 
lean_free_object(x_40);
lean_dec_ref(x_32);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_48);
if (x_66 == 0)
{
return x_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_48, 0);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_48);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_dec(x_40);
lean_inc(x_33);
lean_inc_ref(x_32);
lean_inc_ref(x_26);
x_71 = l_Lean_Compiler_LCNF_ppDecl_x27(x_26, x_32, x_33, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5;
x_75 = l_Lean_Compiler_LCNF_Decl_size(x_26);
x_76 = l_Nat_reprFast(x_75);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_MessageData_ofFormat(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7;
if (lean_is_scalar(x_25)) {
 x_81 = lean_alloc_ctor(7, 2, 0);
} else {
 x_81 = x_25;
 lean_ctor_set_tag(x_81, 7);
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_MessageData_ofFormat(x_72);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(x_28, x_85, x_29, x_32, x_33, x_73);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec_ref(x_86);
x_89 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_87, x_31, x_29, x_32, x_33, x_88);
lean_dec(x_87);
x_13 = x_89;
goto block_18;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_32);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
x_90 = lean_ctor_get(x_71, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_71, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_92 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_94 = lean_ctor_get(x_32, 0);
x_95 = lean_ctor_get(x_32, 1);
x_96 = lean_ctor_get(x_32, 3);
x_97 = lean_ctor_get(x_32, 5);
x_98 = lean_ctor_get(x_32, 6);
x_99 = lean_ctor_get(x_32, 7);
x_100 = lean_ctor_get(x_32, 8);
x_101 = lean_ctor_get(x_32, 9);
x_102 = lean_ctor_get(x_32, 10);
x_103 = lean_ctor_get(x_32, 11);
x_104 = lean_ctor_get_uint8(x_32, sizeof(void*)*13 + 1);
x_105 = lean_ctor_get(x_32, 12);
lean_inc(x_105);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_32);
x_106 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__3;
x_107 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_27, x_106);
x_108 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_108, 0, x_94);
lean_ctor_set(x_108, 1, x_95);
lean_ctor_set(x_108, 2, x_27);
lean_ctor_set(x_108, 3, x_96);
lean_ctor_set(x_108, 4, x_107);
lean_ctor_set(x_108, 5, x_97);
lean_ctor_set(x_108, 6, x_98);
lean_ctor_set(x_108, 7, x_99);
lean_ctor_set(x_108, 8, x_100);
lean_ctor_set(x_108, 9, x_101);
lean_ctor_set(x_108, 10, x_102);
lean_ctor_set(x_108, 11, x_103);
lean_ctor_set(x_108, 12, x_105);
lean_ctor_set_uint8(x_108, sizeof(void*)*13, x_30);
lean_ctor_set_uint8(x_108, sizeof(void*)*13 + 1, x_104);
lean_inc(x_28);
x_109 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__0___redArg(x_28, x_108, x_34);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_28);
lean_dec(x_25);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec_ref(x_109);
x_113 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_1, x_31, x_29, x_108, x_33, x_112);
x_13 = x_113;
goto block_18;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_115 = x_109;
} else {
 lean_dec_ref(x_109);
 x_115 = lean_box(0);
}
lean_inc(x_33);
lean_inc_ref(x_108);
lean_inc_ref(x_26);
x_116 = l_Lean_Compiler_LCNF_ppDecl_x27(x_26, x_108, x_33, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5;
x_120 = l_Lean_Compiler_LCNF_Decl_size(x_26);
x_121 = l_Nat_reprFast(x_120);
x_122 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l_Lean_MessageData_ofFormat(x_122);
if (lean_is_scalar(x_115)) {
 x_124 = lean_alloc_ctor(7, 2, 0);
} else {
 x_124 = x_115;
 lean_ctor_set_tag(x_124, 7);
}
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7;
if (lean_is_scalar(x_25)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_25;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_MessageData_ofFormat(x_117);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(x_28, x_130, x_29, x_108, x_33, x_118);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec_ref(x_131);
x_134 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_132, x_31, x_29, x_108, x_33, x_133);
lean_dec(x_132);
x_13 = x_134;
goto block_18;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_115);
lean_dec_ref(x_108);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
x_135 = lean_ctor_get(x_116, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_116, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_137 = x_116;
} else {
 lean_dec_ref(x_116);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
}
block_172:
{
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_st_ref_take(x_141, x_144);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec_ref(x_149);
x_152 = !lean_is_exclusive(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_ctor_get(x_150, 0);
x_154 = lean_ctor_get(x_150, 5);
lean_dec(x_154);
x_155 = l_Lean_Kernel_enableDiag(x_153, x_146);
x_156 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__12;
lean_ctor_set(x_150, 5, x_156);
lean_ctor_set(x_150, 0, x_155);
x_157 = lean_st_ref_set(x_141, x_150, x_151);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec_ref(x_157);
x_27 = x_140;
x_28 = x_142;
x_29 = x_143;
x_30 = x_146;
x_31 = x_147;
x_32 = x_145;
x_33 = x_141;
x_34 = x_158;
goto block_139;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_159 = lean_ctor_get(x_150, 0);
x_160 = lean_ctor_get(x_150, 1);
x_161 = lean_ctor_get(x_150, 2);
x_162 = lean_ctor_get(x_150, 3);
x_163 = lean_ctor_get(x_150, 4);
x_164 = lean_ctor_get(x_150, 6);
x_165 = lean_ctor_get(x_150, 7);
x_166 = lean_ctor_get(x_150, 8);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_150);
x_167 = l_Lean_Kernel_enableDiag(x_159, x_146);
x_168 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__12;
x_169 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_160);
lean_ctor_set(x_169, 2, x_161);
lean_ctor_set(x_169, 3, x_162);
lean_ctor_set(x_169, 4, x_163);
lean_ctor_set(x_169, 5, x_168);
lean_ctor_set(x_169, 6, x_164);
lean_ctor_set(x_169, 7, x_165);
lean_ctor_set(x_169, 8, x_166);
x_170 = lean_st_ref_set(x_141, x_169, x_151);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec_ref(x_170);
x_27 = x_140;
x_28 = x_142;
x_29 = x_143;
x_30 = x_146;
x_31 = x_147;
x_32 = x_145;
x_33 = x_141;
x_34 = x_171;
goto block_139;
}
}
else
{
x_27 = x_140;
x_28 = x_142;
x_29 = x_143;
x_30 = x_146;
x_31 = x_147;
x_32 = x_145;
x_33 = x_141;
x_34 = x_144;
goto block_139;
}
}
block_191:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; 
x_178 = lean_st_ref_get(x_176, x_177);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = lean_ctor_get(x_175, 2);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 0);
lean_inc_ref(x_182);
lean_dec(x_179);
x_183 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__13;
lean_inc(x_3);
x_184 = l_Lean_Name_append(x_183, x_3);
x_185 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__17;
x_186 = 0;
x_187 = l_Lean_KVMap_setBool(x_181, x_185, x_186);
x_188 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__18;
x_189 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_187, x_188);
x_190 = l_Lean_Kernel_isDiagnosticsEnabled(x_182);
lean_dec_ref(x_182);
if (x_190 == 0)
{
if (x_189 == 0)
{
x_140 = x_187;
x_141 = x_176;
x_142 = x_184;
x_143 = x_174;
x_144 = x_180;
x_145 = x_175;
x_146 = x_189;
x_147 = x_173;
x_148 = x_19;
goto block_172;
}
else
{
x_140 = x_187;
x_141 = x_176;
x_142 = x_184;
x_143 = x_174;
x_144 = x_180;
x_145 = x_175;
x_146 = x_189;
x_147 = x_173;
x_148 = x_190;
goto block_172;
}
}
else
{
x_140 = x_187;
x_141 = x_176;
x_142 = x_184;
x_143 = x_174;
x_144 = x_180;
x_145 = x_175;
x_146 = x_189;
x_147 = x_173;
x_148 = x_189;
goto block_172;
}
}
}
block_18:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
{
size_t _tmp_5 = x_16;
lean_object* _tmp_6 = x_1;
lean_object* _tmp_11 = x_14;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_192; 
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__2;
x_22 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__0___redArg(x_21, x_10, x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_array_uget(x_4, x_6);
x_192 = lean_unbox(x_23);
lean_dec(x_23);
if (x_192 == 0)
{
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_173 = x_8;
x_174 = x_9;
x_175 = x_10;
x_176 = x_11;
x_177 = x_24;
goto block_191;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_193 = lean_ctor_get(x_26, 0);
lean_inc(x_193);
x_194 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_195 = l_Lean_MessageData_ofName(x_193);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__20;
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_Compiler_LCNF_Decl_size(x_26);
x_200 = l_Nat_reprFast(x_199);
x_201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = l_Lean_MessageData_ofFormat(x_201);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_194);
x_205 = l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(x_21, x_204, x_9, x_10, x_11, x_24);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec_ref(x_205);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_173 = x_8;
x_174 = x_9;
x_175 = x_10;
x_176 = x_11;
x_177 = x_206;
goto block_191;
}
block_139:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_32, 4);
lean_dec(x_36);
x_37 = lean_ctor_get(x_32, 2);
lean_dec(x_37);
x_38 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__3;
x_39 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_31, x_38);
lean_ctor_set(x_32, 4, x_39);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*13, x_28);
lean_inc(x_30);
x_40 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__0___redArg(x_30, x_32, x_34);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
lean_dec(x_25);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_1, x_29, x_27, x_32, x_33, x_43);
x_13 = x_44;
goto block_18;
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 1);
x_47 = lean_ctor_get(x_40, 0);
lean_dec(x_47);
lean_inc(x_33);
lean_inc_ref(x_32);
lean_inc_ref(x_26);
x_48 = l_Lean_Compiler_LCNF_ppDecl_x27(x_26, x_32, x_33, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5;
x_52 = l_Lean_Compiler_LCNF_Decl_size(x_26);
x_53 = l_Nat_reprFast(x_52);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_MessageData_ofFormat(x_54);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_55);
lean_ctor_set(x_40, 0, x_51);
x_56 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7;
if (lean_is_scalar(x_25)) {
 x_57 = lean_alloc_ctor(7, 2, 0);
} else {
 x_57 = x_25;
 lean_ctor_set_tag(x_57, 7);
}
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_49);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(x_30, x_61, x_27, x_32, x_33, x_50);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_63, x_29, x_27, x_32, x_33, x_64);
lean_dec(x_63);
x_13 = x_65;
goto block_18;
}
else
{
uint8_t x_66; 
lean_free_object(x_40);
lean_dec_ref(x_32);
lean_dec(x_33);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_48);
if (x_66 == 0)
{
return x_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_48, 0);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_48);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_dec(x_40);
lean_inc(x_33);
lean_inc_ref(x_32);
lean_inc_ref(x_26);
x_71 = l_Lean_Compiler_LCNF_ppDecl_x27(x_26, x_32, x_33, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5;
x_75 = l_Lean_Compiler_LCNF_Decl_size(x_26);
x_76 = l_Nat_reprFast(x_75);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_MessageData_ofFormat(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7;
if (lean_is_scalar(x_25)) {
 x_81 = lean_alloc_ctor(7, 2, 0);
} else {
 x_81 = x_25;
 lean_ctor_set_tag(x_81, 7);
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_MessageData_ofFormat(x_72);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(x_30, x_85, x_27, x_32, x_33, x_73);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec_ref(x_86);
x_89 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_87, x_29, x_27, x_32, x_33, x_88);
lean_dec(x_87);
x_13 = x_89;
goto block_18;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_32);
lean_dec(x_33);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
x_90 = lean_ctor_get(x_71, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_71, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_92 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_94 = lean_ctor_get(x_32, 0);
x_95 = lean_ctor_get(x_32, 1);
x_96 = lean_ctor_get(x_32, 3);
x_97 = lean_ctor_get(x_32, 5);
x_98 = lean_ctor_get(x_32, 6);
x_99 = lean_ctor_get(x_32, 7);
x_100 = lean_ctor_get(x_32, 8);
x_101 = lean_ctor_get(x_32, 9);
x_102 = lean_ctor_get(x_32, 10);
x_103 = lean_ctor_get(x_32, 11);
x_104 = lean_ctor_get_uint8(x_32, sizeof(void*)*13 + 1);
x_105 = lean_ctor_get(x_32, 12);
lean_inc(x_105);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_32);
x_106 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__3;
x_107 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_31, x_106);
x_108 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_108, 0, x_94);
lean_ctor_set(x_108, 1, x_95);
lean_ctor_set(x_108, 2, x_31);
lean_ctor_set(x_108, 3, x_96);
lean_ctor_set(x_108, 4, x_107);
lean_ctor_set(x_108, 5, x_97);
lean_ctor_set(x_108, 6, x_98);
lean_ctor_set(x_108, 7, x_99);
lean_ctor_set(x_108, 8, x_100);
lean_ctor_set(x_108, 9, x_101);
lean_ctor_set(x_108, 10, x_102);
lean_ctor_set(x_108, 11, x_103);
lean_ctor_set(x_108, 12, x_105);
lean_ctor_set_uint8(x_108, sizeof(void*)*13, x_28);
lean_ctor_set_uint8(x_108, sizeof(void*)*13 + 1, x_104);
lean_inc(x_30);
x_109 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__0___redArg(x_30, x_108, x_34);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_30);
lean_dec(x_25);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec_ref(x_109);
x_113 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_1, x_29, x_27, x_108, x_33, x_112);
x_13 = x_113;
goto block_18;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_115 = x_109;
} else {
 lean_dec_ref(x_109);
 x_115 = lean_box(0);
}
lean_inc(x_33);
lean_inc_ref(x_108);
lean_inc_ref(x_26);
x_116 = l_Lean_Compiler_LCNF_ppDecl_x27(x_26, x_108, x_33, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5;
x_120 = l_Lean_Compiler_LCNF_Decl_size(x_26);
x_121 = l_Nat_reprFast(x_120);
x_122 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l_Lean_MessageData_ofFormat(x_122);
if (lean_is_scalar(x_115)) {
 x_124 = lean_alloc_ctor(7, 2, 0);
} else {
 x_124 = x_115;
 lean_ctor_set_tag(x_124, 7);
}
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7;
if (lean_is_scalar(x_25)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_25;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_MessageData_ofFormat(x_117);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(x_30, x_130, x_27, x_108, x_33, x_118);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec_ref(x_131);
x_134 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_2, x_1, x_26, x_132, x_29, x_27, x_108, x_33, x_133);
lean_dec(x_132);
x_13 = x_134;
goto block_18;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_115);
lean_dec_ref(x_108);
lean_dec(x_33);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
x_135 = lean_ctor_get(x_116, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_116, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_137 = x_116;
} else {
 lean_dec_ref(x_116);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
}
block_172:
{
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_st_ref_take(x_140, x_146);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec_ref(x_149);
x_152 = !lean_is_exclusive(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_ctor_get(x_150, 0);
x_154 = lean_ctor_get(x_150, 5);
lean_dec(x_154);
x_155 = l_Lean_Kernel_enableDiag(x_153, x_143);
x_156 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__12;
lean_ctor_set(x_150, 5, x_156);
lean_ctor_set(x_150, 0, x_155);
x_157 = lean_st_ref_set(x_140, x_150, x_151);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec_ref(x_157);
x_27 = x_141;
x_28 = x_143;
x_29 = x_144;
x_30 = x_145;
x_31 = x_147;
x_32 = x_142;
x_33 = x_140;
x_34 = x_158;
goto block_139;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_159 = lean_ctor_get(x_150, 0);
x_160 = lean_ctor_get(x_150, 1);
x_161 = lean_ctor_get(x_150, 2);
x_162 = lean_ctor_get(x_150, 3);
x_163 = lean_ctor_get(x_150, 4);
x_164 = lean_ctor_get(x_150, 6);
x_165 = lean_ctor_get(x_150, 7);
x_166 = lean_ctor_get(x_150, 8);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_150);
x_167 = l_Lean_Kernel_enableDiag(x_159, x_143);
x_168 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__12;
x_169 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_160);
lean_ctor_set(x_169, 2, x_161);
lean_ctor_set(x_169, 3, x_162);
lean_ctor_set(x_169, 4, x_163);
lean_ctor_set(x_169, 5, x_168);
lean_ctor_set(x_169, 6, x_164);
lean_ctor_set(x_169, 7, x_165);
lean_ctor_set(x_169, 8, x_166);
x_170 = lean_st_ref_set(x_140, x_169, x_151);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec_ref(x_170);
x_27 = x_141;
x_28 = x_143;
x_29 = x_144;
x_30 = x_145;
x_31 = x_147;
x_32 = x_142;
x_33 = x_140;
x_34 = x_171;
goto block_139;
}
}
else
{
x_27 = x_141;
x_28 = x_143;
x_29 = x_144;
x_30 = x_145;
x_31 = x_147;
x_32 = x_142;
x_33 = x_140;
x_34 = x_146;
goto block_139;
}
}
block_191:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; 
x_178 = lean_st_ref_get(x_176, x_177);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = lean_ctor_get(x_175, 2);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 0);
lean_inc_ref(x_182);
lean_dec(x_179);
x_183 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__13;
lean_inc(x_3);
x_184 = l_Lean_Name_append(x_183, x_3);
x_185 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__17;
x_186 = 0;
x_187 = l_Lean_KVMap_setBool(x_181, x_185, x_186);
x_188 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__18;
x_189 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_187, x_188);
x_190 = l_Lean_Kernel_isDiagnosticsEnabled(x_182);
lean_dec_ref(x_182);
if (x_190 == 0)
{
if (x_189 == 0)
{
x_140 = x_176;
x_141 = x_174;
x_142 = x_175;
x_143 = x_189;
x_144 = x_173;
x_145 = x_184;
x_146 = x_180;
x_147 = x_187;
x_148 = x_19;
goto block_172;
}
else
{
x_140 = x_176;
x_141 = x_174;
x_142 = x_175;
x_143 = x_189;
x_144 = x_173;
x_145 = x_184;
x_146 = x_180;
x_147 = x_187;
x_148 = x_190;
goto block_172;
}
}
else
{
x_140 = x_176;
x_141 = x_174;
x_142 = x_175;
x_143 = x_189;
x_144 = x_173;
x_145 = x_184;
x_146 = x_180;
x_147 = x_187;
x_148 = x_189;
goto block_172;
}
}
}
block_18:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_16, x_1, x_8, x_9, x_10, x_11, x_14);
return x_17;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___redArg(x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_array_size(x_2);
x_11 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___redArg(x_9, x_3, x_1, x_2, x_10, x_11, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
if (x_3 == 0)
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec_ref(x_12);
x_18 = l_Lean_Compiler_LCNF_checkDeadLocalDecls(x_2, x_4, x_5, x_6, x_7, x_17);
return x_18;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___redArg(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_2);
x_18 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_19 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_19, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Compiler_LCNF_checkpoint(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isValidMainType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PUnit", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isValidMainType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_isValidMainType___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isValidMainType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt32", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isValidMainType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_isValidMainType___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isValidMainType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isValidMainType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_isValidMainType___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isValidMainType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isValidMainType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isValidMainType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String", 6, 6);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isValidMainType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_7; 
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Compiler_LCNF_isValidMainType___closed__6;
x_19 = lean_string_dec_eq(x_17, x_18);
if (x_19 == 0)
{
return x_19;
}
else
{
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
x_7 = x_20;
goto block_12;
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
case 7:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_25) == 5)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get(x_25, 1);
x_31 = lean_ctor_get(x_27, 1);
x_32 = l_Lean_Compiler_LCNF_isValidMainType___closed__7;
x_33 = lean_string_dec_eq(x_31, x_32);
if (x_33 == 0)
{
return x_33;
}
else
{
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = l_Lean_Compiler_LCNF_isValidMainType___closed__8;
x_38 = lean_string_dec_eq(x_36, x_37);
if (x_38 == 0)
{
return x_38;
}
else
{
if (lean_obj_tag(x_29) == 5)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_29, 0);
if (lean_obj_tag(x_39) == 4)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_29, 1);
x_43 = lean_ctor_get(x_40, 1);
x_44 = l_Lean_Compiler_LCNF_isValidMainType___closed__6;
x_45 = lean_string_dec_eq(x_43, x_44);
if (x_45 == 0)
{
return x_45;
}
else
{
if (lean_obj_tag(x_42) == 4)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_42, 0);
x_7 = x_46;
goto block_12;
}
else
{
uint8_t x_47; 
x_47 = 0;
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = 0;
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = 0;
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = 0;
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = 0;
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = 0;
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = 0;
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = 0;
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = 0;
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = 0;
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = 0;
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = 0;
return x_58;
}
}
default: 
{
uint8_t x_59; 
x_59 = 0;
return x_59;
}
}
block_6:
{
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Compiler_LCNF_isValidMainType___closed__1;
x_5 = lean_name_eq(x_2, x_4);
return x_5;
}
else
{
return x_3;
}
}
block_12:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Compiler_LCNF_isValidMainType___closed__3;
x_9 = lean_name_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Compiler_LCNF_isValidMainType___closed__5;
x_11 = lean_name_eq(x_7, x_10);
x_2 = x_7;
x_3 = x_11;
goto block_6;
}
else
{
x_2 = x_7;
x_3 = x_9;
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isValidMainType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_isValidMainType(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`main` function must have type `(List String →)\? IO (UInt32 | Unit | PUnit)`", 78, 76);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_5, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_array_uget(x_3, x_5);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__1;
x_21 = lean_name_eq(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_19);
x_11 = x_1;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_19, x_9, x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 0)
{
x_11 = x_1;
x_12 = x_24;
goto block_16;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec_ref(x_23);
x_30 = l_Lean_ConstantInfo_type(x_29);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_isValidMainType(x_30);
lean_dec_ref(x_30);
if (x_31 == 0)
{
x_25 = x_21;
goto block_28;
}
else
{
x_25 = x_2;
goto block_28;
}
}
block_28:
{
if (x_25 == 0)
{
x_11 = x_1;
x_12 = x_24;
goto block_16;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__3;
x_27 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_26, x_7, x_8, x_9, x_24);
return x_27;
}
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_5, x_13);
x_5 = x_14;
x_6 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_array_uget(x_3, x_5);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__1;
x_22 = lean_name_eq(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_20);
x_12 = x_1;
x_13 = x_11;
goto block_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_20, x_10, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
if (lean_obj_tag(x_24) == 0)
{
x_12 = x_1;
x_13 = x_25;
goto block_17;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec_ref(x_24);
x_31 = l_Lean_ConstantInfo_type(x_30);
lean_dec(x_30);
x_32 = l_Lean_Compiler_LCNF_isValidMainType(x_31);
lean_dec_ref(x_31);
if (x_32 == 0)
{
x_26 = x_22;
goto block_29;
}
else
{
x_26 = x_2;
goto block_29;
}
}
block_29:
{
if (x_26 == 0)
{
x_12 = x_1;
x_13 = x_25;
goto block_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__3;
x_28 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_27, x_8, x_9, x_10, x_25);
return x_28;
}
}
}
}
block_17:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_15, x_12, x_8, x_9, x_10, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_12 = l_Lean_Compiler_LCNF_toDecl(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_16, x_2, x_13);
x_2 = x_18;
x_3 = x_19;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__0;
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
x_16 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__2;
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
x_23 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__2;
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
x_39 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__2;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_6, 2);
x_10 = lean_st_ref_get(x_7, x_8);
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
x_15 = lean_st_ref_get(x_7, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_st_ref_get(x_5, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_21);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_dec(x_24);
x_25 = lean_st_ref_take(x_7, x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 4);
lean_inc_ref(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_26, 4);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_34 = lean_ctor_get(x_27, 0);
lean_dec(x_34);
x_35 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_36 = lean_array_size(x_35);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_36, x_37, x_35);
x_39 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_23);
lean_dec_ref(x_23);
x_41 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
lean_inc(x_9);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_21);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_9);
lean_ctor_set_tag(x_25, 3);
lean_ctor_set(x_25, 1, x_39);
lean_ctor_set(x_25, 0, x_42);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_3);
x_43 = l_Lean_PersistentArray_push___redArg(x_1, x_19);
lean_ctor_set(x_27, 0, x_43);
x_44 = lean_st_ref_set(x_7, x_26, x_29);
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
uint64_t x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_51 = lean_ctor_get_uint64(x_27, sizeof(void*)*1);
lean_dec(x_27);
x_52 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_53 = lean_array_size(x_52);
x_54 = 0;
x_55 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_53, x_54, x_52);
x_56 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_4);
lean_ctor_set(x_56, 2, x_55);
x_57 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_23);
lean_dec_ref(x_23);
x_58 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
lean_inc(x_9);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_21);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_tag(x_25, 3);
lean_ctor_set(x_25, 1, x_56);
lean_ctor_set(x_25, 0, x_59);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_3);
x_60 = l_Lean_PersistentArray_push___redArg(x_1, x_19);
x_61 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint64(x_61, sizeof(void*)*1, x_51);
lean_ctor_set(x_26, 4, x_61);
x_62 = lean_st_ref_set(x_7, x_26, x_29);
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
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint64_t x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_67 = lean_ctor_get(x_26, 0);
x_68 = lean_ctor_get(x_26, 1);
x_69 = lean_ctor_get(x_26, 2);
x_70 = lean_ctor_get(x_26, 3);
x_71 = lean_ctor_get(x_26, 5);
x_72 = lean_ctor_get(x_26, 6);
x_73 = lean_ctor_get(x_26, 7);
x_74 = lean_ctor_get(x_26, 8);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_26);
x_75 = lean_ctor_get_uint64(x_27, sizeof(void*)*1);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_76 = x_27;
} else {
 lean_dec_ref(x_27);
 x_76 = lean_box(0);
}
x_77 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_78 = lean_array_size(x_77);
x_79 = 0;
x_80 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_78, x_79, x_77);
x_81 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_4);
lean_ctor_set(x_81, 2, x_80);
x_82 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_23);
lean_dec_ref(x_23);
x_83 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
lean_inc(x_9);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_21);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_9);
lean_ctor_set_tag(x_25, 3);
lean_ctor_set(x_25, 1, x_81);
lean_ctor_set(x_25, 0, x_84);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_3);
x_85 = l_Lean_PersistentArray_push___redArg(x_1, x_19);
if (lean_is_scalar(x_76)) {
 x_86 = lean_alloc_ctor(0, 1, 8);
} else {
 x_86 = x_76;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set_uint64(x_86, sizeof(void*)*1, x_75);
x_87 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_87, 0, x_67);
lean_ctor_set(x_87, 1, x_68);
lean_ctor_set(x_87, 2, x_69);
lean_ctor_set(x_87, 3, x_70);
lean_ctor_set(x_87, 4, x_86);
lean_ctor_set(x_87, 5, x_71);
lean_ctor_set(x_87, 6, x_72);
lean_ctor_set(x_87, 7, x_73);
lean_ctor_set(x_87, 8, x_74);
x_88 = lean_st_ref_set(x_7, x_87, x_29);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_93 = lean_ctor_get(x_25, 1);
lean_inc(x_93);
lean_dec(x_25);
x_94 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_26, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_26, 2);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_26, 3);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_26, 5);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_26, 6);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_26, 7);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_26, 8);
lean_inc_ref(x_101);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 lean_ctor_release(x_26, 6);
 lean_ctor_release(x_26, 7);
 lean_ctor_release(x_26, 8);
 x_102 = x_26;
} else {
 lean_dec_ref(x_26);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get_uint64(x_27, sizeof(void*)*1);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_104 = x_27;
} else {
 lean_dec_ref(x_27);
 x_104 = lean_box(0);
}
x_105 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_106 = lean_array_size(x_105);
x_107 = 0;
x_108 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_106, x_107, x_105);
x_109 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_109, 0, x_2);
lean_ctor_set(x_109, 1, x_4);
lean_ctor_set(x_109, 2, x_108);
x_110 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_23);
lean_dec_ref(x_23);
x_111 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
lean_inc(x_9);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_21);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_112, 3, x_9);
x_113 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_19, 1, x_113);
lean_ctor_set(x_19, 0, x_3);
x_114 = l_Lean_PersistentArray_push___redArg(x_1, x_19);
if (lean_is_scalar(x_104)) {
 x_115 = lean_alloc_ctor(0, 1, 8);
} else {
 x_115 = x_104;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set_uint64(x_115, sizeof(void*)*1, x_103);
if (lean_is_scalar(x_102)) {
 x_116 = lean_alloc_ctor(0, 9, 0);
} else {
 x_116 = x_102;
}
lean_ctor_set(x_116, 0, x_94);
lean_ctor_set(x_116, 1, x_95);
lean_ctor_set(x_116, 2, x_96);
lean_ctor_set(x_116, 3, x_97);
lean_ctor_set(x_116, 4, x_115);
lean_ctor_set(x_116, 5, x_98);
lean_ctor_set(x_116, 6, x_99);
lean_ctor_set(x_116, 7, x_100);
lean_ctor_set(x_116, 8, x_101);
x_117 = lean_st_ref_set(x_7, x_116, x_93);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint64_t x_137; lean_object* x_138; lean_object* x_139; size_t x_140; size_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_122 = lean_ctor_get(x_19, 0);
lean_inc(x_122);
lean_dec(x_19);
x_123 = lean_st_ref_take(x_7, x_20);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 4);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_124, 0);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_124, 2);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_124, 3);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_124, 5);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_124, 6);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_124, 7);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_124, 8);
lean_inc_ref(x_135);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 lean_ctor_release(x_124, 6);
 lean_ctor_release(x_124, 7);
 lean_ctor_release(x_124, 8);
 x_136 = x_124;
} else {
 lean_dec_ref(x_124);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get_uint64(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_138 = x_125;
} else {
 lean_dec_ref(x_125);
 x_138 = lean_box(0);
}
x_139 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_140 = lean_array_size(x_139);
x_141 = 0;
x_142 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_140, x_141, x_139);
x_143 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_143, 0, x_2);
lean_ctor_set(x_143, 1, x_4);
lean_ctor_set(x_143, 2, x_142);
x_144 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_122);
lean_dec_ref(x_122);
x_145 = l_Lean_Compiler_LCNF_shouldGenerateCode___closed__7;
lean_inc(x_9);
x_146 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_146, 0, x_21);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_144);
lean_ctor_set(x_146, 3, x_9);
if (lean_is_scalar(x_127)) {
 x_147 = lean_alloc_ctor(3, 2, 0);
} else {
 x_147 = x_127;
 lean_ctor_set_tag(x_147, 3);
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_143);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_3);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_PersistentArray_push___redArg(x_1, x_148);
if (lean_is_scalar(x_138)) {
 x_150 = lean_alloc_ctor(0, 1, 8);
} else {
 x_150 = x_138;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set_uint64(x_150, sizeof(void*)*1, x_137);
if (lean_is_scalar(x_136)) {
 x_151 = lean_alloc_ctor(0, 9, 0);
} else {
 x_151 = x_136;
}
lean_ctor_set(x_151, 0, x_128);
lean_ctor_set(x_151, 1, x_129);
lean_ctor_set(x_151, 2, x_130);
lean_ctor_set(x_151, 3, x_131);
lean_ctor_set(x_151, 4, x_150);
lean_ctor_set(x_151, 5, x_132);
lean_ctor_set(x_151, 6, x_133);
lean_ctor_set(x_151, 7, x_134);
lean_ctor_set(x_151, 8, x_135);
x_152 = lean_st_ref_set(x_7, x_151, x_126);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
x_155 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4___redArg(x_1, x_5, x_2, x_3, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(x_4, x_13);
return x_14;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__5() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__6() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHeartbeats;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; double x_15; double x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; lean_object* x_29; double x_30; double x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_45; lean_object* x_46; double x_47; uint8_t x_48; double x_49; lean_object* x_50; lean_object* x_51; lean_object* x_60; lean_object* x_61; lean_object* x_62; double x_63; uint8_t x_64; double x_65; lean_object* x_66; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; double x_82; double x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; uint8_t x_88; lean_object* x_127; lean_object* x_128; lean_object* x_129; double x_130; double x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; double x_135; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; double x_165; uint8_t x_166; double x_167; lean_object* x_168; uint8_t x_169; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; double x_212; uint8_t x_213; double x_214; lean_object* x_215; double x_216; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; uint8_t x_271; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 5);
lean_inc(x_12);
lean_inc(x_1);
x_77 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__0___redArg(x_1, x_8, x_10);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_271 = lean_unbox(x_78);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__3;
x_273 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_11, x_272);
if (x_273 == 0)
{
lean_object* x_274; 
lean_dec(x_78);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_274 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_79);
return x_274;
}
else
{
goto block_270;
}
}
else
{
goto block_270;
}
block_27:
{
if (x_17 == 0)
{
double x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__0;
x_21 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set_float(x_21, sizeof(void*)*2, x_20);
lean_ctor_set_float(x_21, sizeof(void*)*2 + 8, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 16, x_4);
x_22 = lean_box(0);
x_23 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___lam__0(x_13, x_12, x_18, x_14, x_21, x_22, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_16);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_15);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_4);
x_25 = lean_box(0);
x_26 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___lam__0(x_13, x_12, x_18, x_14, x_24, x_25, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_14);
return x_26;
}
}
block_44:
{
lean_object* x_35; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_35 = lean_apply_6(x_2, x_33, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_35) == 0)
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_13 = x_28;
x_14 = x_29;
x_15 = x_31;
x_16 = x_30;
x_17 = x_34;
x_18 = x_36;
x_19 = x_37;
goto block_27;
}
else
{
uint8_t x_38; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_ctor_set_tag(x_35, 1);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec_ref(x_35);
x_43 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__2;
x_13 = x_28;
x_14 = x_29;
x_15 = x_31;
x_16 = x_30;
x_17 = x_34;
x_18 = x_43;
x_19 = x_42;
goto block_27;
}
}
block_59:
{
if (x_48 == 0)
{
double x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__0;
x_53 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_5);
lean_ctor_set_float(x_53, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_53, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 16, x_4);
x_54 = lean_box(0);
x_55 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___lam__0(x_46, x_12, x_50, x_45, x_53, x_54, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_45);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_5);
lean_ctor_set_float(x_56, sizeof(void*)*2, x_47);
lean_ctor_set_float(x_56, sizeof(void*)*2 + 8, x_49);
lean_ctor_set_uint8(x_56, sizeof(void*)*2 + 16, x_4);
x_57 = lean_box(0);
x_58 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___lam__0(x_46, x_12, x_50, x_45, x_56, x_57, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_45);
return x_58;
}
}
block_76:
{
lean_object* x_67; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_67 = lean_apply_6(x_2, x_62, x_6, x_7, x_8, x_9, x_66);
if (lean_obj_tag(x_67) == 0)
{
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_45 = x_60;
x_46 = x_61;
x_47 = x_63;
x_48 = x_64;
x_49 = x_65;
x_50 = x_68;
x_51 = x_69;
goto block_59;
}
else
{
uint8_t x_70; 
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_ctor_set_tag(x_67, 1);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_dec_ref(x_67);
x_75 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__2;
x_45 = x_60;
x_46 = x_61;
x_47 = x_63;
x_48 = x_64;
x_49 = x_65;
x_50 = x_75;
x_51 = x_74;
goto block_59;
}
}
block_126:
{
uint8_t x_89; 
x_89 = lean_unbox(x_78);
lean_dec(x_78);
if (x_89 == 0)
{
if (x_88 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec(x_12);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_90 = lean_st_ref_take(x_9, x_85);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 4);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec_ref(x_90);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_91, 4);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_92, 0);
x_98 = l_Lean_PersistentArray_append___redArg(x_84, x_97);
lean_dec_ref(x_97);
lean_ctor_set(x_92, 0, x_98);
x_99 = lean_st_ref_set(x_9, x_91, x_93);
lean_dec(x_9);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(x_87, x_100);
lean_dec_ref(x_87);
return x_101;
}
else
{
uint64_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get_uint64(x_92, sizeof(void*)*1);
x_103 = lean_ctor_get(x_92, 0);
lean_inc(x_103);
lean_dec(x_92);
x_104 = l_Lean_PersistentArray_append___redArg(x_84, x_103);
lean_dec_ref(x_103);
x_105 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set_uint64(x_105, sizeof(void*)*1, x_102);
lean_ctor_set(x_91, 4, x_105);
x_106 = lean_st_ref_set(x_9, x_91, x_93);
lean_dec(x_9);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(x_87, x_107);
lean_dec_ref(x_87);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_109 = lean_ctor_get(x_91, 0);
x_110 = lean_ctor_get(x_91, 1);
x_111 = lean_ctor_get(x_91, 2);
x_112 = lean_ctor_get(x_91, 3);
x_113 = lean_ctor_get(x_91, 5);
x_114 = lean_ctor_get(x_91, 6);
x_115 = lean_ctor_get(x_91, 7);
x_116 = lean_ctor_get(x_91, 8);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_91);
x_117 = lean_ctor_get_uint64(x_92, sizeof(void*)*1);
x_118 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_118);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_119 = x_92;
} else {
 lean_dec_ref(x_92);
 x_119 = lean_box(0);
}
x_120 = l_Lean_PersistentArray_append___redArg(x_84, x_118);
lean_dec_ref(x_118);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 1, 8);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_uint64(x_121, sizeof(void*)*1, x_117);
x_122 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_122, 0, x_109);
lean_ctor_set(x_122, 1, x_110);
lean_ctor_set(x_122, 2, x_111);
lean_ctor_set(x_122, 3, x_112);
lean_ctor_set(x_122, 4, x_121);
lean_ctor_set(x_122, 5, x_113);
lean_ctor_set(x_122, 6, x_114);
lean_ctor_set(x_122, 7, x_115);
lean_ctor_set(x_122, 8, x_116);
x_123 = lean_st_ref_set(x_9, x_122, x_93);
lean_dec(x_9);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(x_87, x_124);
lean_dec_ref(x_87);
return x_125;
}
}
else
{
lean_dec_ref(x_84);
x_28 = x_80;
x_29 = x_81;
x_30 = x_83;
x_31 = x_82;
x_32 = x_85;
x_33 = x_87;
x_34 = x_86;
goto block_44;
}
}
else
{
lean_dec_ref(x_84);
x_28 = x_80;
x_29 = x_81;
x_30 = x_83;
x_31 = x_82;
x_32 = x_85;
x_33 = x_87;
x_34 = x_86;
goto block_44;
}
}
block_138:
{
double x_136; uint8_t x_137; 
x_136 = lean_float_sub(x_131, x_130);
x_137 = lean_float_decLt(x_135, x_136);
x_80 = x_127;
x_81 = x_128;
x_82 = x_131;
x_83 = x_130;
x_84 = x_129;
x_85 = x_132;
x_86 = x_134;
x_87 = x_133;
x_88 = x_137;
goto block_126;
}
block_160:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; double x_148; double x_149; lean_object* x_150; uint8_t x_151; 
x_145 = lean_io_get_num_heartbeats(x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec_ref(x_145);
x_148 = lean_float_of_nat(x_140);
x_149 = lean_float_of_nat(x_146);
x_150 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__3;
x_151 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_11, x_150);
if (x_151 == 0)
{
lean_dec(x_11);
lean_inc_ref(x_143);
x_80 = x_139;
x_81 = x_143;
x_82 = x_149;
x_83 = x_148;
x_84 = x_141;
x_85 = x_147;
x_86 = x_151;
x_87 = x_143;
x_88 = x_151;
goto block_126;
}
else
{
if (x_142 == 0)
{
lean_object* x_152; lean_object* x_153; double x_154; double x_155; double x_156; 
x_152 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__4;
x_153 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_11, x_152);
lean_dec(x_11);
x_154 = lean_float_of_nat(x_153);
x_155 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__5;
x_156 = lean_float_div(x_154, x_155);
lean_inc_ref(x_143);
x_127 = x_139;
x_128 = x_143;
x_129 = x_141;
x_130 = x_148;
x_131 = x_149;
x_132 = x_147;
x_133 = x_143;
x_134 = x_151;
x_135 = x_156;
goto block_138;
}
else
{
lean_object* x_157; lean_object* x_158; double x_159; 
x_157 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__4;
x_158 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_11, x_157);
lean_dec(x_11);
x_159 = lean_float_of_nat(x_158);
lean_inc_ref(x_143);
x_127 = x_139;
x_128 = x_143;
x_129 = x_141;
x_130 = x_148;
x_131 = x_149;
x_132 = x_147;
x_133 = x_143;
x_134 = x_151;
x_135 = x_159;
goto block_138;
}
}
}
block_207:
{
uint8_t x_170; 
x_170 = lean_unbox(x_78);
lean_dec(x_78);
if (x_170 == 0)
{
if (x_169 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec(x_12);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_171 = lean_st_ref_take(x_9, x_168);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 4);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec_ref(x_171);
x_175 = !lean_is_exclusive(x_172);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_172, 4);
lean_dec(x_176);
x_177 = !lean_is_exclusive(x_173);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_178 = lean_ctor_get(x_173, 0);
x_179 = l_Lean_PersistentArray_append___redArg(x_164, x_178);
lean_dec_ref(x_178);
lean_ctor_set(x_173, 0, x_179);
x_180 = lean_st_ref_set(x_9, x_172, x_174);
lean_dec(x_9);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(x_163, x_181);
lean_dec_ref(x_163);
return x_182;
}
else
{
uint64_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_183 = lean_ctor_get_uint64(x_173, sizeof(void*)*1);
x_184 = lean_ctor_get(x_173, 0);
lean_inc(x_184);
lean_dec(x_173);
x_185 = l_Lean_PersistentArray_append___redArg(x_164, x_184);
lean_dec_ref(x_184);
x_186 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set_uint64(x_186, sizeof(void*)*1, x_183);
lean_ctor_set(x_172, 4, x_186);
x_187 = lean_st_ref_set(x_9, x_172, x_174);
lean_dec(x_9);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(x_163, x_188);
lean_dec_ref(x_163);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint64_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_190 = lean_ctor_get(x_172, 0);
x_191 = lean_ctor_get(x_172, 1);
x_192 = lean_ctor_get(x_172, 2);
x_193 = lean_ctor_get(x_172, 3);
x_194 = lean_ctor_get(x_172, 5);
x_195 = lean_ctor_get(x_172, 6);
x_196 = lean_ctor_get(x_172, 7);
x_197 = lean_ctor_get(x_172, 8);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_172);
x_198 = lean_ctor_get_uint64(x_173, sizeof(void*)*1);
x_199 = lean_ctor_get(x_173, 0);
lean_inc_ref(x_199);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_200 = x_173;
} else {
 lean_dec_ref(x_173);
 x_200 = lean_box(0);
}
x_201 = l_Lean_PersistentArray_append___redArg(x_164, x_199);
lean_dec_ref(x_199);
if (lean_is_scalar(x_200)) {
 x_202 = lean_alloc_ctor(0, 1, 8);
} else {
 x_202 = x_200;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set_uint64(x_202, sizeof(void*)*1, x_198);
x_203 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_203, 0, x_190);
lean_ctor_set(x_203, 1, x_191);
lean_ctor_set(x_203, 2, x_192);
lean_ctor_set(x_203, 3, x_193);
lean_ctor_set(x_203, 4, x_202);
lean_ctor_set(x_203, 5, x_194);
lean_ctor_set(x_203, 6, x_195);
lean_ctor_set(x_203, 7, x_196);
lean_ctor_set(x_203, 8, x_197);
x_204 = lean_st_ref_set(x_9, x_203, x_174);
lean_dec(x_9);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(x_163, x_205);
lean_dec_ref(x_163);
return x_206;
}
}
else
{
lean_dec_ref(x_164);
x_60 = x_161;
x_61 = x_162;
x_62 = x_163;
x_63 = x_165;
x_64 = x_166;
x_65 = x_167;
x_66 = x_168;
goto block_76;
}
}
else
{
lean_dec_ref(x_164);
x_60 = x_161;
x_61 = x_162;
x_62 = x_163;
x_63 = x_165;
x_64 = x_166;
x_65 = x_167;
x_66 = x_168;
goto block_76;
}
}
block_219:
{
double x_217; uint8_t x_218; 
x_217 = lean_float_sub(x_214, x_212);
x_218 = lean_float_decLt(x_216, x_217);
x_161 = x_208;
x_162 = x_209;
x_163 = x_210;
x_164 = x_211;
x_165 = x_212;
x_166 = x_213;
x_167 = x_214;
x_168 = x_215;
x_169 = x_218;
goto block_207;
}
block_244:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; double x_229; double x_230; double x_231; double x_232; double x_233; lean_object* x_234; uint8_t x_235; 
x_226 = lean_io_mono_nanos_now(x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec_ref(x_226);
x_229 = lean_float_of_nat(x_221);
x_230 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__6;
x_231 = lean_float_div(x_229, x_230);
x_232 = lean_float_of_nat(x_227);
x_233 = lean_float_div(x_232, x_230);
x_234 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__3;
x_235 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_11, x_234);
if (x_235 == 0)
{
lean_dec(x_11);
lean_inc_ref(x_224);
x_161 = x_224;
x_162 = x_220;
x_163 = x_224;
x_164 = x_222;
x_165 = x_231;
x_166 = x_235;
x_167 = x_233;
x_168 = x_228;
x_169 = x_235;
goto block_207;
}
else
{
if (x_223 == 0)
{
lean_object* x_236; lean_object* x_237; double x_238; double x_239; double x_240; 
x_236 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__4;
x_237 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_11, x_236);
lean_dec(x_11);
x_238 = lean_float_of_nat(x_237);
x_239 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__5;
x_240 = lean_float_div(x_238, x_239);
lean_inc_ref(x_224);
x_208 = x_224;
x_209 = x_220;
x_210 = x_224;
x_211 = x_222;
x_212 = x_231;
x_213 = x_235;
x_214 = x_233;
x_215 = x_228;
x_216 = x_240;
goto block_219;
}
else
{
lean_object* x_241; lean_object* x_242; double x_243; 
x_241 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__4;
x_242 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_11, x_241);
lean_dec(x_11);
x_243 = lean_float_of_nat(x_242);
lean_inc_ref(x_224);
x_208 = x_224;
x_209 = x_220;
x_210 = x_224;
x_211 = x_222;
x_212 = x_231;
x_213 = x_235;
x_214 = x_233;
x_215 = x_228;
x_216 = x_243;
goto block_219;
}
}
}
block_270:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_245 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg(x_9, x_79);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec_ref(x_245);
x_248 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__7;
x_249 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_11, x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_io_mono_nanos_now(x_247);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec_ref(x_250);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_253 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec_ref(x_253);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_254);
lean_inc(x_246);
x_220 = x_246;
x_221 = x_251;
x_222 = x_246;
x_223 = x_249;
x_224 = x_256;
x_225 = x_255;
goto block_244;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_253, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 1);
lean_inc(x_258);
lean_dec_ref(x_253);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_257);
lean_inc(x_246);
x_220 = x_246;
x_221 = x_251;
x_222 = x_246;
x_223 = x_249;
x_224 = x_259;
x_225 = x_258;
goto block_244;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_io_get_num_heartbeats(x_247);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec_ref(x_260);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_263 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_262);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec_ref(x_263);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_264);
lean_inc(x_246);
x_139 = x_246;
x_140 = x_261;
x_141 = x_246;
x_142 = x_249;
x_143 = x_266;
x_144 = x_265;
goto block_160;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
lean_dec_ref(x_263);
x_269 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_269, 0, x_267);
lean_inc(x_246);
x_139 = x_246;
x_140 = x_261;
x_141 = x_246;
x_142 = x_249;
x_143 = x_269;
x_144 = x_268;
goto block_160;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler phase: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", pass: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("base", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mono", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__1;
if (x_8 == 0)
{
lean_object* x_23; 
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__4;
x_11 = x_23;
goto block_22;
}
else
{
lean_object* x_24; 
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__5;
x_11 = x_24;
goto block_22;
}
block_22:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__3;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofName(x_9);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_1);
x_10 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_1);
x_13 = lean_apply_6(x_2, x_3, x_12, x_5, x_6, x_7, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*3 + 1);
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*3 + 2);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_18);
x_19 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___boxed), 7, 1);
lean_closure_set(x_19, 0, x_13);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__13;
x_21 = lean_box(x_14);
x_22 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__1___boxed), 8, 3);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_18);
lean_closure_set(x_22, 2, x_5);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__8;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_24 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg(x_20, x_19, x_22, x_11, x_23, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
if (x_1 == 0)
{
x_27 = x_16;
goto block_39;
}
else
{
x_27 = x_11;
goto block_39;
}
block_39:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_28);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_15);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_30 = l_Lean_Compiler_LCNF_checkpoint(x_17, x_25, x_27, x_29, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; size_t x_32; size_t x_33; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_5 = x_25;
x_10 = x_31;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_5, x_4);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_3, x_5);
lean_inc(x_9);
lean_inc_ref(x_8);
x_14 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_13, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_15);
x_17 = l_Lean_Compiler_LCNF_ppDecl_x27(x_15, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5;
x_21 = l_Lean_Compiler_LCNF_Decl_size(x_15);
lean_dec(x_15);
x_22 = l_Nat_reprFast(x_21);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofFormat(x_18);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_1);
x_32 = l_Lean_addTrace___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__1___redArg(x_1, x_31, x_7, x_8, x_9, x_19);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = 1;
x_35 = lean_usize_add(x_5, x_34);
{
size_t _tmp_4 = x_35;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_9 = x_33;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_10 = _tmp_9;
}
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
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
uint8_t x_41; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
return x_14;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_shouldGenerateCode(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_18 = lean_unbox(x_11);
lean_dec(x_11);
if (x_18 == 0)
{
lean_dec(x_9);
x_13 = x_4;
goto block_17;
}
else
{
lean_object* x_19; 
x_19 = lean_array_push(x_4, x_9);
x_13 = x_19;
goto block_17;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_13;
x_7 = x_12;
goto _start;
}
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_compiler_check;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_PassManager_run___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PassManager_run___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_84; lean_object* x_85; uint8_t x_100; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 7);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 8);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 9);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 10);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_28 = lean_ctor_get(x_4, 11);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_30 = lean_ctor_get(x_4, 12);
lean_inc_ref(x_30);
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
 x_31 = x_4;
} else {
 lean_dec_ref(x_4);
 x_31 = lean_box(0);
}
x_32 = lean_unsigned_to_nat(8192u);
x_33 = lean_unsigned_to_nat(0u);
x_84 = lean_array_get_size(x_1);
x_100 = lean_nat_dec_le(x_32, x_20);
if (x_100 == 0)
{
lean_dec(x_20);
x_85 = x_32;
goto block_99;
}
else
{
x_85 = x_20;
goto block_99;
}
block_15:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
x_11 = l_Lean_IR_toIR(x_7, x_8, x_9, x_10);
lean_dec_ref(x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_IR_compile(x_12, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_14;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
return x_11;
}
}
block_83:
{
uint8_t x_37; 
x_37 = l_Array_isEmpty___redArg(x_35);
if (x_37 == 0)
{
lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_array_size(x_35);
x_40 = 0;
x_41 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(x_38, x_37, x_35, x_39, x_40, x_38, x_2, x_3, x_34, x_5, x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_5);
lean_inc_ref(x_34);
lean_inc(x_3);
lean_inc_ref(x_2);
x_43 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__2(x_39, x_40, x_35, x_2, x_3, x_34, x_5, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; size_t x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Lean_Compiler_LCNF_getPassManager___redArg(x_5, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Lean_Compiler_LCNF_markRecDecls(x_44);
x_50 = l_Lean_Compiler_LCNF_PassManager_run___closed__0;
x_51 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_18, x_50);
lean_dec(x_18);
x_52 = lean_array_size(x_47);
lean_inc(x_5);
lean_inc_ref(x_34);
lean_inc(x_3);
x_53 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7(x_51, x_47, x_52, x_40, x_49, x_2, x_3, x_34, x_5, x_48);
lean_dec(x_47);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Compiler_LCNF_PassManager_run___closed__2;
x_57 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_inferVisibility_markPublic_spec__0___redArg(x_56, x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_3);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec_ref(x_57);
x_7 = x_54;
x_8 = x_34;
x_9 = x_5;
x_10 = x_60;
goto block_15;
}
else
{
lean_object* x_61; size_t x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec_ref(x_57);
x_62 = lean_array_size(x_54);
lean_inc(x_5);
lean_inc_ref(x_34);
x_63 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___redArg(x_56, x_38, x_54, x_62, x_40, x_38, x_3, x_34, x_5, x_61);
lean_dec(x_3);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_7 = x_54;
x_8 = x_34;
x_9 = x_5;
x_10 = x_64;
goto block_15;
}
else
{
uint8_t x_65; 
lean_dec(x_54);
lean_dec_ref(x_34);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_34);
lean_dec(x_5);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_53);
if (x_69 == 0)
{
return x_53;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_53, 0);
x_71 = lean_ctor_get(x_53, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_53);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec_ref(x_34);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_73 = !lean_is_exclusive(x_43);
if (x_73 == 0)
{
return x_43;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_43, 0);
x_75 = lean_ctor_get(x_43, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_43);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_77 = !lean_is_exclusive(x_41);
if (x_77 == 0)
{
return x_41;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_41, 0);
x_79 = lean_ctor_get(x_41, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_41);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_81 = l_Lean_Compiler_LCNF_PassManager_run___closed__3;
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_36);
return x_82;
}
}
block_99:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_inc(x_18);
if (lean_is_scalar(x_31)) {
 x_86 = lean_alloc_ctor(0, 13, 2);
} else {
 x_86 = x_31;
}
lean_ctor_set(x_86, 0, x_16);
lean_ctor_set(x_86, 1, x_17);
lean_ctor_set(x_86, 2, x_18);
lean_ctor_set(x_86, 3, x_19);
lean_ctor_set(x_86, 4, x_85);
lean_ctor_set(x_86, 5, x_21);
lean_ctor_set(x_86, 6, x_22);
lean_ctor_set(x_86, 7, x_23);
lean_ctor_set(x_86, 8, x_24);
lean_ctor_set(x_86, 9, x_25);
lean_ctor_set(x_86, 10, x_26);
lean_ctor_set(x_86, 11, x_28);
lean_ctor_set(x_86, 12, x_30);
lean_ctor_set_uint8(x_86, sizeof(void*)*13, x_27);
lean_ctor_set_uint8(x_86, sizeof(void*)*13 + 1, x_29);
x_87 = l_Lean_Compiler_LCNF_PassManager_run___closed__4;
x_88 = lean_nat_dec_lt(x_33, x_84);
if (x_88 == 0)
{
lean_dec(x_84);
x_34 = x_86;
x_35 = x_87;
x_36 = x_6;
goto block_83;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_84, x_84);
if (x_89 == 0)
{
lean_dec(x_84);
x_34 = x_86;
x_35 = x_87;
x_36 = x_6;
goto block_83;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_84);
lean_dec(x_84);
lean_inc(x_5);
lean_inc_ref(x_86);
x_92 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9___redArg(x_1, x_90, x_91, x_87, x_86, x_5, x_6);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_34 = x_86;
x_35 = x_93;
x_36 = x_94;
goto block_83;
}
else
{
uint8_t x_95; 
lean_dec_ref(x_86);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_95 = !lean_is_exclusive(x_92);
if (x_95 == 0)
{
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 0);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_92);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(x_1, x_11, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0(x_1, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(x_1, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_4);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0(x_1, x_2, x_3, x_14, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__2(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__9(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PassManager_run(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_compile___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_compile___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_compile___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_compile___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_compile___closed__4;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_compile___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Compiler_LCNF_compile___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassManager_run___boxed), 6, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Compiler_LCNF_compile___closed__6;
x_7 = 0;
x_8 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_5, x_6, x_7, x_2, x_3, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_showDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<not-available>", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_showDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_showDecl___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Compiler_LCNF_getDeclAt_x3f___redArg(x_2, x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l_Lean_Compiler_LCNF_showDecl___closed__1;
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Lean_Compiler_LCNF_showDecl___closed__1;
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
lean_dec_ref(x_6);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec_ref(x_7);
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
x_7 = l_Lean_Compiler_LCNF_showDecl(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_main___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiling: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_main___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_main___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_Compiler_LCNF_main___lam__0___closed__1;
x_7 = lean_array_to_list(x_1);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(x_7, x_8);
x_10 = l_Lean_MessageData_ofList(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PassManager_run(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_main___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compilation", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_lcnf_compile_decls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_main___lam__0___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Compiler_LCNF_main___closed__0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__13;
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_main___lam__1___boxed), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Compiler_LCNF_compile___closed__6;
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CompilerM_run___boxed), 7, 4);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, x_10);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_13);
x_15 = 1;
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__8;
x_17 = lean_box(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___boxed), 9, 6);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_8);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_14);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_16);
x_19 = lean_box(0);
x_20 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_7, x_5, x_18, x_19, x_2, x_3, x_4);
lean_dec(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_main___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_main___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2012u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("test", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("jp", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Main___hyg_2012_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_2012_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Compiler_LCNF_PassManager_run___closed__2;
x_11 = l_Lean_registerTraceClass(x_10, x_3, x_4, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Main___hyg_2012_;
x_14 = 0;
x_15 = l_Lean_registerTraceClass(x_13, x_14, x_4, x_12);
return x_15;
}
else
{
return x_11;
}
}
else
{
return x_8;
}
}
else
{
return x_5;
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
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__0);
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
l_Lean_Compiler_LCNF_shouldGenerateCode___closed__27 = _init_l_Lean_Compiler_LCNF_shouldGenerateCode___closed__27();
lean_mark_persistent(l_Lean_Compiler_LCNF_shouldGenerateCode___closed__27);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__3);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__4);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__5);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__6);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__7);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__8);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__9);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__10 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__10();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__10);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__11 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__11();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__11);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__12 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__12();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__12);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__13 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__13();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__13);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__14 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__14();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__14);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__15 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__15();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__15);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__16 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__16();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__16);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__17 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__17();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__17);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__18 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__18();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__18);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__19 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__19();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__19);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__20 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__20();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___closed__20);
l_Lean_Compiler_LCNF_isValidMainType___closed__0 = _init_l_Lean_Compiler_LCNF_isValidMainType___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_isValidMainType___closed__0);
l_Lean_Compiler_LCNF_isValidMainType___closed__1 = _init_l_Lean_Compiler_LCNF_isValidMainType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_isValidMainType___closed__1);
l_Lean_Compiler_LCNF_isValidMainType___closed__2 = _init_l_Lean_Compiler_LCNF_isValidMainType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_isValidMainType___closed__2);
l_Lean_Compiler_LCNF_isValidMainType___closed__3 = _init_l_Lean_Compiler_LCNF_isValidMainType___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_isValidMainType___closed__3);
l_Lean_Compiler_LCNF_isValidMainType___closed__4 = _init_l_Lean_Compiler_LCNF_isValidMainType___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_isValidMainType___closed__4);
l_Lean_Compiler_LCNF_isValidMainType___closed__5 = _init_l_Lean_Compiler_LCNF_isValidMainType___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_isValidMainType___closed__5);
l_Lean_Compiler_LCNF_isValidMainType___closed__6 = _init_l_Lean_Compiler_LCNF_isValidMainType___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_isValidMainType___closed__6);
l_Lean_Compiler_LCNF_isValidMainType___closed__7 = _init_l_Lean_Compiler_LCNF_isValidMainType___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_isValidMainType___closed__7);
l_Lean_Compiler_LCNF_isValidMainType___closed__8 = _init_l_Lean_Compiler_LCNF_isValidMainType___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_isValidMainType___closed__8);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___closed__3);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3_spec__3___redArg___closed__2);
l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__0 = _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__0();
l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__1 = _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__1);
l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__2 = _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__2);
l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__3 = _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__3);
l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__4 = _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__4();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__4);
l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__5 = _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__5();
l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__6 = _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__6();
l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__7 = _init_l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__7();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__3___redArg___closed__7);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__3);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__4);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__7___lam__0___closed__5);
l_Lean_Compiler_LCNF_PassManager_run___closed__0 = _init_l_Lean_Compiler_LCNF_PassManager_run___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___closed__0);
l_Lean_Compiler_LCNF_PassManager_run___closed__1 = _init_l_Lean_Compiler_LCNF_PassManager_run___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___closed__1);
l_Lean_Compiler_LCNF_PassManager_run___closed__2 = _init_l_Lean_Compiler_LCNF_PassManager_run___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___closed__2);
l_Lean_Compiler_LCNF_PassManager_run___closed__3 = _init_l_Lean_Compiler_LCNF_PassManager_run___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___closed__3);
l_Lean_Compiler_LCNF_PassManager_run___closed__4 = _init_l_Lean_Compiler_LCNF_PassManager_run___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_PassManager_run___closed__4);
l_Lean_Compiler_LCNF_compile___closed__0 = _init_l_Lean_Compiler_LCNF_compile___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__0);
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
l_Lean_Compiler_LCNF_compile___closed__6 = _init_l_Lean_Compiler_LCNF_compile___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_compile___closed__6);
l_Lean_Compiler_LCNF_showDecl___closed__0 = _init_l_Lean_Compiler_LCNF_showDecl___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_showDecl___closed__0);
l_Lean_Compiler_LCNF_showDecl___closed__1 = _init_l_Lean_Compiler_LCNF_showDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_showDecl___closed__1);
l_Lean_Compiler_LCNF_main___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_main___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_main___lam__0___closed__0);
l_Lean_Compiler_LCNF_main___lam__0___closed__1 = _init_l_Lean_Compiler_LCNF_main___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_main___lam__0___closed__1);
l_Lean_Compiler_LCNF_main___closed__0 = _init_l_Lean_Compiler_LCNF_main___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_main___closed__0);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
l_Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Main___hyg_2012_ = _init_l_Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Main___hyg_2012_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Main___hyg_2012_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_2012_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
